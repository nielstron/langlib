module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem
public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

@[expose]
public section

/-!
# Context-sensitive languages are closed under inverse homomorphism

The proof uses fixed-width blocks.  For a homomorphism `h : A → List B`, one physical
input cell stores the (bounded) list `h a`.  Empty blocks are allowed.  A cellwise finite
verifier checks one move of the target LBA on the logical tape obtained by concatenating the
nonempty positions of all blocks.  `CertifiedRowSystem` then compiles the verifier to an
input-sized LBA.

This construction is uniform in both finite alphabet types; no distinguished letters or
fixed witness alphabets are used.
-/

open List Relation Classical

noncomputable section

namespace CSInverseHomomorphism

open LBA CertifiedRowSystem

variable {A B Γ Λ : Type}

private abbrev VSym (B Γ : Type) := LBA.EndAlpha B Γ
private abbrev VCell (B Γ Λ : Type) := VSym B Γ × Option Λ

/-! ## The semantic logical-tape step -/

private def quiet {B Γ Λ : Type} (xs : List (VSym B Γ)) : List (VCell B Γ Λ) :=
  xs.map fun a => (a, none)

private inductive VirtualStep (M : LBA.Machine (VSym B Γ) Λ) :
    List (VCell B Γ Λ) → List (VCell B Γ Λ) → Prop
  | stay (pre post : List (VSym B Γ)) (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.stay) ∈ M.transition q a) :
      VirtualStep M
        (quiet pre ++ (a, some q) :: quiet post)
        (quiet pre ++ (a', some q') :: quiet post)
  | leftClamp (post : List (VSym B Γ)) (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
      VirtualStep M
        ((a, some q) :: quiet post)
        ((a', some q') :: quiet post)
  | left (pre : List (VSym B Γ)) (b : VSym B Γ) (post : List (VSym B Γ))
      (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
      VirtualStep M
        (quiet pre ++ (b, none) :: (a, some q) :: quiet post)
        (quiet pre ++ (b, some q') :: (a', none) :: quiet post)
  | right (pre : List (VSym B Γ)) (q q' : Λ) (a a' b : VSym B Γ)
      (post : List (VSym B Γ))
      (htr : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
      VirtualStep M
        (quiet pre ++ (a, some q) :: (b, none) :: quiet post)
        (quiet pre ++ (a', none) :: (b, some q') :: quiet post)
  | rightClamp (pre : List (VSym B Γ)) (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
      VirtualStep M
        (quiet pre ++ [(a, some q)])
        (quiet pre ++ [(a', some q')])

private inductive TailStep (M : LBA.Machine (VSym B Γ) Λ) :
    List (VCell B Γ Λ) → List (VCell B Γ Λ) → Prop
  | stay (pre post : List (VSym B Γ)) (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.stay) ∈ M.transition q a) :
      TailStep M
        (quiet pre ++ (a, some q) :: quiet post)
        (quiet pre ++ (a', some q') :: quiet post)
  | left (pre : List (VSym B Γ)) (b : VSym B Γ) (post : List (VSym B Γ))
      (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
      TailStep M
        (quiet pre ++ (b, none) :: (a, some q) :: quiet post)
        (quiet pre ++ (b, some q') :: (a', none) :: quiet post)
  | right (pre : List (VSym B Γ)) (q q' : Λ) (a a' b : VSym B Γ)
      (post : List (VSym B Γ))
      (htr : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
      TailStep M
        (quiet pre ++ (a, some q) :: (b, none) :: quiet post)
        (quiet pre ++ (a', none) :: (b, some q') :: quiet post)
  | rightClamp (pre : List (VSym B Γ)) (q q' : Λ) (a a' : VSym B Γ)
      (htr : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
      TailStep M
        (quiet pre ++ [(a, some q)])
        (quiet pre ++ [(a', some q')])

private lemma TailStep.toVirtual {M : LBA.Machine (VSym B Γ) Λ} {old new}
    (h : TailStep M old new) : VirtualStep M old new := by
  cases h with
  | stay pre post q q' a a' htr => exact .stay pre post q q' a a' htr
  | left pre b post q q' a a' htr => exact .left pre b post q q' a a' htr
  | right pre q q' a a' b post htr => exact .right pre q q' a a' b post htr
  | rightClamp pre q q' a a' htr => exact .rightClamp pre q q' a a' htr

/-! ## A finite checker for `VirtualStep` -/

private inductive Role (Λ : Type) where
  | same
  | stay
  | leftClamp
  | leftDest
  | leftSource
  | rightSource (q' : Λ)
  | rightDest
  | rightClamp
deriving Fintype, DecidableEq

private inductive ScanState (Λ : Type) where
  | first
  | before
  | needLeftSource (q' : Λ)
  | needRightDest (q' : Λ)
  | rightClampCandidate
  | done
  | bad
deriving Fintype, DecidableEq

private def scanSlot (M : LBA.Machine (VSym B Γ) Λ) :
    ScanState Λ → Option (VCell B Γ Λ) → Option (VCell B Γ Λ) →
      Role Λ → ScanState Λ
  | .bad, _, _, _ => .bad
  | s, none, none, .same => s
  | .before, some (a, none), some (b, none), .same =>
      if a = b then .before else .bad
  | .first, some (a, none), some (b, none), .same =>
      if a = b then .before else .bad
  | .done, some (a, none), some (b, none), .same =>
      if a = b then .done else .bad
  | s, some (a, some q), some (a', some q'), .stay =>
      if s = .first ∨ s = .before then
        if (q', a', DLBA.Dir.stay) ∈ M.transition q a then .done else .bad
      else .bad
  | .first, some (a, some q), some (a', some q'), .leftClamp =>
      if (q', a', DLBA.Dir.left) ∈ M.transition q a then .done else .bad
  | .first, some (a, none), some (a', some q'), .leftDest =>
      if a = a' then .needLeftSource q' else .bad
  | .before, some (a, none), some (a', some q'), .leftDest =>
      if a = a' then .needLeftSource q' else .bad
  | .needLeftSource q', some (a, some q), some (a', none), .leftSource =>
      if (q', a', DLBA.Dir.left) ∈ M.transition q a then .done else .bad
  | s, some (a, some q), some (a', none), .rightSource q' =>
      if s = .first ∨ s = .before then
        if (q', a', DLBA.Dir.right) ∈ M.transition q a then .needRightDest q' else .bad
      else .bad
  | .needRightDest q', some (a, none), some (a', some q''), .rightDest =>
      if a = a' ∧ q' = q'' then .done else .bad
  | s, some (a, some q), some (a', some q'), .rightClamp =>
      if s = .first ∨ s = .before then
        if (q', a', DLBA.Dir.right) ∈ M.transition q a then .rightClampCandidate else .bad
      else .bad
  | _, _, _, _ => .bad

private def scanList (M : LBA.Machine (VSym B Γ) Λ) :
    ScanState Λ → List (Option (VCell B Γ Λ)) →
      List (Option (VCell B Γ Λ)) → List (Role Λ) → Option (ScanState Λ)
  | q, [], [], [] => some q
  | q, a :: as, b :: bs, r :: rs => scanList M (scanSlot M q a b r) as bs rs
  | _, _, _, _ => none

private def scanAccept : ScanState Λ → Bool
  | .done | .rightClampCandidate => true
  | _ => false

@[simp] private lemma scanSlot_bad (M : LBA.Machine (VSym B Γ) Λ)
    (old new : Option (VCell B Γ Λ)) (role : Role Λ) :
    scanSlot M .bad old new role = .bad := by
  cases old <;> cases new <;> cases role <;> rfl

@[simp] private lemma scanSlot_none_none_same
    (M : LBA.Machine (VSym B Γ) Λ) (s : ScanState Λ) :
    scanSlot M s none none .same = s := by
  cases s <;> rfl

@[simp] private lemma scanSlot_none_none_ne
    (M : LBA.Machine (VSym B Γ) Λ) (s : ScanState Λ) (role : Role Λ)
    (hrole : role ≠ .same) :
    scanSlot M s none none role = .bad := by
  cases s <;> cases role <;> simp_all [scanSlot]

@[simp] private lemma scanSlot_none_some
    (M : LBA.Machine (VSym B Γ) Λ) (s : ScanState Λ)
    (new : VCell B Γ Λ) (role : Role Λ) :
    scanSlot M s none (some new) role = .bad := by
  rcases new with ⟨a, q⟩
  cases s <;> cases q <;> cases role <;> rfl

@[simp] private lemma scanSlot_some_none
    (M : LBA.Machine (VSym B Γ) Λ) (s : ScanState Λ)
    (old : VCell B Γ Λ) (role : Role Λ) :
    scanSlot M s (some old) none role = .bad := by
  rcases old with ⟨a, q⟩
  cases s <;> cases q <;> cases role <;> rfl

private def denseScan (M : LBA.Machine (VSym B Γ) Λ) (s : ScanState Λ)
    (old new : List (VCell B Γ Λ)) (roles : List (Role Λ)) : Option (ScanState Λ) :=
  scanList M s (old.map some) (new.map some) roles

private def DenseRun (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (VCell B Γ Λ)) : Prop :=
  ∃ roles s, denseScan M .first old new roles = some s ∧ scanAccept s = true

private lemma scanList_bad_noaccept (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (Option (VCell B Γ Λ))) (roles : List (Role Λ))
    (s : ScanState Λ) (hscan : scanList M .bad old new roles = some s)
    (hacc : scanAccept s = true) : False := by
  induction old generalizing new roles with
  | nil =>
      cases new <;> cases roles <;> simp [scanList] at hscan
      subst s
      simp [scanAccept] at hacc
  | cons x xs ih =>
    cases new with
      | nil => simp [scanList] at hscan
      | cons y ys =>
        cases roles with
        | nil => simp [scanList] at hscan
        | cons r rs =>
          simp only [scanList, scanSlot_bad] at hscan
          exact ih ys rs hscan

private lemma denseScan_done_iff (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M .done old new roles = some s ∧ scanAccept s = true) ↔
      ∃ xs : List (VSym B Γ), old = quiet xs ∧ new = quiet xs := by
  induction old generalizing new with
  | nil =>
      constructor
      · rintro ⟨roles, s, hscan, hs⟩
        cases new <;> cases roles <;> simp [denseScan, scanList, scanAccept] at hscan hs
        exact ⟨[], rfl, rfl⟩
      · rintro ⟨xs, hxs, hnew⟩
        have hlen := congrArg List.length hxs
        have hxs' : xs = [] := List.length_eq_zero_iff.mp (by simpa [quiet] using hlen.symm)
        subst xs
        simp [quiet] at hnew
        subst new
        exact ⟨[], .done, rfl, rfl⟩
  | cons x old ih =>
      constructor
      · rintro ⟨roles, s, hscan, hs⟩
        cases new with
        | nil => cases roles <;> simp [denseScan, scanList] at hscan
        | cons y new =>
          cases roles with
          | nil => simp [denseScan, scanList] at hscan
          | cons r roles =>
            cases x with
            | mk a oq =>
              cases oq with
              | none =>
                cases y with
                | mk b oq' =>
                  cases oq' with
                  | none =>
                    cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                    case same =>
                      split at hscan
                      · rename_i hab
                        subst b
                        have ht : ∃ rs t, denseScan M .done old new rs = some t ∧
                            scanAccept t = true := ⟨roles, s, hscan, hs⟩
                        rcases (ih new).mp ht with ⟨xs, hold, hnew⟩
                        exact ⟨a :: xs, by simp [quiet, hold], by simp [quiet, hnew]⟩
                      · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                    all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  | some q' =>
                    cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                    all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
              | some q =>
                cases y with
                | mk b oq' =>
                  cases oq' <;> cases r <;>
                    simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
      · rintro ⟨xs, hold, hnew⟩
        cases xs with
        | nil => simp [quiet] at hold
        | cons a xs =>
          simp only [quiet, List.map_cons, List.cons.injEq] at hold hnew
          rcases hold with ⟨rfl, hold⟩
          rcases hnew with ⟨rfl, hnew⟩
          subst old
          rcases (ih (quiet xs)).mpr ⟨xs, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
          exact ⟨Role.same :: roles, s, by
            simp only [denseScan, List.map_cons, scanList, scanSlot]
            exact hscan, hs⟩

private lemma denseScan_rightClampCandidate_iff
    (M : LBA.Machine (VSym B Γ) Λ) (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M .rightClampCandidate old new roles = some s ∧
      scanAccept s = true) ↔ old = [] ∧ new = [] := by
  constructor
  · rintro ⟨roles, s, hscan, hs⟩
    cases old with
    | nil =>
      cases new <;> cases roles <;> simp [denseScan, scanList, scanAccept] at hscan hs ⊢
    | cons x xs =>
      cases new with
      | nil => cases roles <;> simp [denseScan, scanList] at hscan
      | cons y ys =>
        cases roles with
        | nil => simp [denseScan, scanList] at hscan
        | cons r rs =>
          cases x with
          | mk a oq =>
            cases oq <;> cases y with
            | mk b oq' =>
              cases oq' <;> cases r <;>
                simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
              all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], .rightClampCandidate, rfl, rfl⟩

private lemma denseScan_needRight_iff
    (M : LBA.Machine (VSym B Γ) Λ) (q' : Λ)
    (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M (.needRightDest q') old new roles = some s ∧
      scanAccept s = true) ↔
      ∃ (a : VSym B Γ) (post : List (VSym B Γ)),
        old = (a, none) :: quiet post ∧ new = (a, some q') :: quiet post := by
  constructor
  · rintro ⟨roles, s, hscan, hs⟩
    cases old with
    | nil =>
      cases new <;> cases roles <;> simp [denseScan, scanList] at hscan
      subst s
      simp [scanAccept] at hs
    | cons x xs =>
      cases new with
      | nil => cases roles <;> simp [denseScan, scanList] at hscan
      | cons y ys =>
        cases roles with
        | nil => simp [denseScan, scanList] at hscan
        | cons r rs =>
          cases x with
          | mk a oq =>
            cases oq with
            | none =>
              cases y with
              | mk b oq' =>
                cases oq' with
                | none =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                | some q'' =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case rightDest =>
                    split at hscan
                    · rename_i heq
                      rcases heq with ⟨rfl, rfl⟩
                      have ht : ∃ roles s, denseScan M .done xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_done_iff M xs ys).mp ht with ⟨post, hx, hy⟩
                      exact ⟨a, post, by simp [hx], by simp [hy]⟩
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
            | some q =>
              cases y with
              | mk b oq' =>
                cases oq' <;> cases r <;>
                  simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
  · rintro ⟨a, post, rfl, rfl⟩
    rcases (denseScan_done_iff M (quiet post) (quiet post)).mpr
      ⟨post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
    exact ⟨Role.rightDest :: roles, s, by
      simp only [denseScan, List.map_cons, scanList, scanSlot, and_self, if_true]
      exact hscan, hs⟩

private lemma denseScan_needLeft_iff
    (M : LBA.Machine (VSym B Γ) Λ) (q' : Λ)
    (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M (.needLeftSource q') old new roles = some s ∧
      scanAccept s = true) ↔
      ∃ (a a' : VSym B Γ) (q : Λ) (post : List (VSym B Γ)),
        old = (a, some q) :: quiet post ∧ new = (a', none) :: quiet post ∧
          (q', a', DLBA.Dir.left) ∈ M.transition q a := by
  constructor
  · rintro ⟨roles, s, hscan, hs⟩
    cases old with
    | nil =>
      cases new <;> cases roles <;> simp [denseScan, scanList] at hscan
      subst s
      simp [scanAccept] at hs
    | cons x xs =>
      cases new with
      | nil => cases roles <;> simp [denseScan, scanList] at hscan
      | cons y ys =>
        cases roles with
        | nil => simp [denseScan, scanList] at hscan
        | cons r rs =>
          cases x with
          | mk a oq =>
            cases oq with
            | none =>
              cases y with
              | mk b oq' =>
                cases oq' <;> cases r <;>
                  simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
            | some q =>
              cases y with
              | mk a' oq' =>
                cases oq' with
                | some q'' =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                | none =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case leftSource =>
                    split at hscan
                    · rename_i htr
                      have ht : ∃ roles s, denseScan M .done xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_done_iff M xs ys).mp ht with ⟨post, hx, hy⟩
                      exact ⟨a, a', q, post, by simp [hx], by simp [hy], htr⟩
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
  · rintro ⟨a, a', q, post, rfl, rfl, htr⟩
    rcases (denseScan_done_iff M (quiet post) (quiet post)).mpr
      ⟨post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
    exact ⟨Role.leftSource :: roles, s, by
      simp only [denseScan, List.map_cons, scanList, scanSlot, if_pos htr]
      exact hscan, hs⟩

private lemma denseScan_prependQuiet_before (M : LBA.Machine (VSym B Γ) Λ)
    (pre : List (VSym B Γ)) (old new : List (VCell B Γ Λ))
    (roles : List (Role Λ)) (s : ScanState Λ)
    (hscan : denseScan M .before old new roles = some s) :
    denseScan M .before (quiet pre ++ old) (quiet pre ++ new)
      (List.replicate pre.length Role.same ++ roles) = some s := by
  induction pre with
  | nil => simpa [quiet] using hscan
  | cons a pre ih =>
    simp only [quiet, List.map_cons, List.cons_append, List.length_cons,
      List.replicate_succ, denseScan, List.map_cons, scanList, scanSlot, if_pos rfl]
    exact ih

private lemma tailStep_nonempty {M : LBA.Machine (VSym B Γ) Λ} {old new}
    (h : TailStep M old new) : old ≠ [] := by
  cases h <;> simp [quiet]

private lemma denseScan_before_sound (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M .before old new roles = some s ∧ scanAccept s = true) →
      TailStep M old new := by
  induction old generalizing new with
  | nil =>
    rintro ⟨roles, s, hscan, hs⟩
    cases new <;> cases roles <;> simp [denseScan, scanList] at hscan
    subst s
    simp [scanAccept] at hs
  | cons x xs ih =>
    rintro ⟨roles, s, hscan, hs⟩
    cases new with
    | nil => cases roles <;> simp [denseScan, scanList] at hscan
    | cons y ys =>
      cases roles with
      | nil => simp [denseScan, scanList] at hscan
      | cons r rs =>
        cases x with
        | mk a oq =>
          cases oq with
          | none =>
            cases y with
            | mk b oq' =>
              cases oq' with
              | none =>
                cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                case same =>
                  split at hscan
                  · rename_i hab
                    subst b
                    have ht : ∃ roles s, denseScan M .before xs ys roles = some s ∧
                        scanAccept s = true := ⟨rs, s, hscan, hs⟩
                    have htail := ih ys ht
                    cases htail with
                    | stay pre post q q' c c' htr =>
                      simpa [quiet, List.map_cons, List.append_assoc] using
                        TailStep.stay (M := M) (a :: pre) post q q' c c' htr
                    | left pre c post q q' d d' htr =>
                      simpa [quiet, List.map_cons, List.append_assoc] using
                        TailStep.left (M := M) (a :: pre) c post q q' d d' htr
                    | right pre q q' c c' d post htr =>
                      simpa [quiet, List.map_cons, List.append_assoc] using
                        TailStep.right (M := M) (a :: pre) q q' c c' d post htr
                    | rightClamp pre q q' c c' htr =>
                      simpa [quiet, List.map_cons, List.append_assoc] using
                        TailStep.rightClamp (M := M) (a :: pre) q q' c c' htr
                  · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
              | some q' =>
                cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                case leftDest =>
                  split at hscan
                  · rename_i hab
                    subst b
                    have ht : ∃ roles s,
                        denseScan M (.needLeftSource q') xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                    rcases (denseScan_needLeft_iff M q' xs ys).mp ht with
                      ⟨c, c', q, post, hx, hy, htr⟩
                    subst xs
                    subst ys
                    exact TailStep.left [] a post q q' c c' htr
                  · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
          | some q =>
            cases y with
            | mk b oq' =>
              cases oq' with
              | none =>
                cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                case rightSource q' =>
                  simp only [or_true, if_true] at hscan
                  split at hscan
                  · rename_i htr
                    have ht : ∃ roles s,
                        denseScan M (.needRightDest q') xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                    rcases (denseScan_needRight_iff M q' xs ys).mp ht with
                      ⟨c, post, hx, hy⟩
                    subst xs
                    subst ys
                    exact TailStep.right [] q q' a b c post htr
                  · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
              | some q' =>
                cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                case stay =>
                  simp only [or_true, if_true] at hscan
                  split at hscan
                  · rename_i htr
                    have ht : ∃ roles s, denseScan M .done xs ys roles = some s ∧
                        scanAccept s = true := ⟨rs, s, hscan, hs⟩
                    rcases (denseScan_done_iff M xs ys).mp ht with ⟨post, hx, hy⟩
                    subst xs
                    subst ys
                    exact TailStep.stay [] post q q' a b htr
                  · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                case rightClamp =>
                  simp only [or_true, if_true] at hscan
                  split at hscan
                  · rename_i htr
                    have ht : ∃ roles s,
                        denseScan M .rightClampCandidate xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                    rcases (denseScan_rightClampCandidate_iff M xs ys).mp ht with ⟨rfl, rfl⟩
                    exact TailStep.rightClamp [] q q' a b htr
                  · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
private lemma denseScan_before_complete (M : LBA.Machine (VSym B Γ) Λ)
  {old new : List (VCell B Γ Λ)} (hstep : TailStep M old new) :
  ∃ roles s, denseScan M .before old new roles = some s ∧ scanAccept s = true := by
cases hstep with
  | stay pre post q q' a a' htr =>
        rcases (denseScan_done_iff M (quiet post) (quiet post)).mpr
          ⟨post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
        have hbase : denseScan M .before ((a, some q) :: quiet post)
            ((a', some q') :: quiet post) (Role.stay :: roles) = some s := by
          simp only [denseScan, List.map_cons, scanList, scanSlot]
          simp only [or_true, if_true, htr]
          exact hscan
        exact ⟨List.replicate pre.length Role.same ++ Role.stay :: roles, s,
          denseScan_prependQuiet_before M pre _ _ _ _ hbase, hs⟩
  | left pre b post q q' a a' htr =>
        rcases (denseScan_needLeft_iff M q'
          ((a, some q) :: quiet post) ((a', none) :: quiet post)).mpr
            ⟨a, a', q, post, rfl, rfl, htr⟩ with ⟨roles, s, hscan, hs⟩
        have hbase : denseScan M .before
            ((b, none) :: (a, some q) :: quiet post)
            ((b, some q') :: (a', none) :: quiet post)
            (Role.leftDest :: roles) = some s := by
          simp only [denseScan, List.map_cons, scanList, scanSlot, if_pos rfl]
          exact hscan
        exact ⟨List.replicate pre.length Role.same ++ Role.leftDest :: roles, s,
          denseScan_prependQuiet_before M pre _ _ _ _ hbase, hs⟩
  | right pre q q' a a' b post htr =>
        rcases (denseScan_needRight_iff M q'
          ((b, none) :: quiet post) ((b, some q') :: quiet post)).mpr
            ⟨b, post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
        have hbase : denseScan M .before
            ((a, some q) :: (b, none) :: quiet post)
            ((a', none) :: (b, some q') :: quiet post)
            (Role.rightSource q' :: roles) = some s := by
          simp only [denseScan, List.map_cons, scanList, scanSlot]
          simp only [or_true, if_true, htr]
          exact hscan
        exact ⟨List.replicate pre.length Role.same ++ Role.rightSource q' :: roles, s,
          denseScan_prependQuiet_before M pre _ _ _ _ hbase, hs⟩
  | rightClamp pre q q' a a' htr =>
        have hbase : denseScan M .before [(a, some q)] [(a', some q')]
            [Role.rightClamp] = some .rightClampCandidate := by
          simp only [denseScan, List.map_cons, List.map_nil, scanList, scanSlot]
          simp only [or_true, if_true, htr]
        exact ⟨List.replicate pre.length Role.same ++ [Role.rightClamp],
          .rightClampCandidate, denseScan_prependQuiet_before M pre _ _ _ _ hbase, rfl⟩

private lemma denseScan_before_iff (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (VCell B Γ Λ)) :
    (∃ roles s, denseScan M .before old new roles = some s ∧ scanAccept s = true) ↔
      TailStep M old new :=
  ⟨denseScan_before_sound M old new, denseScan_before_complete M⟩

private lemma denseRun_iff_virtualStep (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (VCell B Γ Λ)) : DenseRun M old new ↔ VirtualStep M old new := by
  constructor
  · rintro ⟨roles, s, hscan, hs⟩
    cases old with
    | nil =>
      cases new <;> cases roles <;> simp [DenseRun, denseScan, scanList] at hscan
      subst s
      simp [scanAccept] at hs
    | cons x xs =>
      cases new with
      | nil => cases roles <;> simp [denseScan, scanList] at hscan
      | cons y ys =>
        cases roles with
        | nil => simp [denseScan, scanList] at hscan
        | cons r rs =>
          cases x with
          | mk a oq =>
            cases oq with
            | none =>
              cases y with
              | mk b oq' =>
                cases oq' with
                | none =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case same =>
                    split at hscan
                    · rename_i hab
                      subst b
                      have ht : ∃ roles s, denseScan M .before xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      have htail := denseScan_before_sound M xs ys ht
                      cases htail with
                      | stay pre post q q' c c' htr =>
                        simpa [quiet, List.map_cons, List.append_assoc] using
                          VirtualStep.stay (M := M) (a :: pre) post q q' c c' htr
                      | left pre c post q q' d d' htr =>
                        simpa [quiet, List.map_cons, List.append_assoc] using
                          VirtualStep.left (M := M) (a :: pre) c post q q' d d' htr
                      | right pre q q' c c' d post htr =>
                        simpa [quiet, List.map_cons, List.append_assoc] using
                          VirtualStep.right (M := M) (a :: pre) q q' c c' d post htr
                      | rightClamp pre q q' c c' htr =>
                        simpa [quiet, List.map_cons, List.append_assoc] using
                          VirtualStep.rightClamp (M := M) (a :: pre) q q' c c' htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                | some q' =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case leftDest =>
                    split at hscan
                    · rename_i hab
                      subst b
                      have ht : ∃ roles s,
                          denseScan M (.needLeftSource q') xs ys roles = some s ∧
                            scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_needLeft_iff M q' xs ys).mp ht with
                        ⟨c, c', q, post, hx, hy, htr⟩
                      subst xs
                      subst ys
                      exact VirtualStep.left [] a post q q' c c' htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
            | some q =>
              cases y with
              | mk b oq' =>
                cases oq' with
                | none =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case rightSource q' =>
                    simp only [true_or, if_true] at hscan
                    split at hscan
                    · rename_i htr
                      have ht : ∃ roles s,
                          denseScan M (.needRightDest q') xs ys roles = some s ∧
                            scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_needRight_iff M q' xs ys).mp ht with
                        ⟨c, post, hx, hy⟩
                      subst xs
                      subst ys
                      exact VirtualStep.right [] q q' a b c post htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                | some q' =>
                  cases r <;> simp only [denseScan, List.map_cons, scanList, scanSlot] at hscan
                  case stay =>
                    simp only [true_or, if_true] at hscan
                    split at hscan
                    · rename_i htr
                      have ht : ∃ roles s, denseScan M .done xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_done_iff M xs ys).mp ht with ⟨post, hx, hy⟩
                      subst xs
                      subst ys
                      exact VirtualStep.stay [] post q q' a b htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  case leftClamp =>
                    split at hscan
                    · rename_i htr
                      have ht : ∃ roles s, denseScan M .done xs ys roles = some s ∧
                          scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_done_iff M xs ys).mp ht with ⟨post, hx, hy⟩
                      subst xs
                      subst ys
                      exact VirtualStep.leftClamp post q q' a b htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  case rightClamp =>
                    simp only [true_or, if_true] at hscan
                    split at hscan
                    · rename_i htr
                      have ht : ∃ roles s,
                          denseScan M .rightClampCandidate xs ys roles = some s ∧
                            scanAccept s = true := ⟨rs, s, hscan, hs⟩
                      rcases (denseScan_rightClampCandidate_iff M xs ys).mp ht with ⟨rfl, rfl⟩
                      exact VirtualStep.rightClamp [] q q' a b htr
                    · exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
                  all_goals exact (scanList_bad_noaccept M _ _ _ s hscan hs).elim
  · intro hstep
    cases hstep with
    | leftClamp post q q' a a' htr =>
      rcases (denseScan_done_iff M (quiet post) (quiet post)).mpr
        ⟨post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
      exact ⟨Role.leftClamp :: roles, s, by
        simp only [denseScan, List.map_cons, scanList, scanSlot, if_pos htr]
        exact hscan, hs⟩
    | stay pre post q q' a a' htr =>
      cases pre with
      | nil =>
        rcases (denseScan_done_iff M (quiet post) (quiet post)).mpr
          ⟨post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.stay :: roles, s, by
          simp only [quiet, List.map_nil, List.nil_append, denseScan, List.map_cons,
            scanList, scanSlot, true_or, if_true, if_pos htr]
          exact hscan, hs⟩

      | cons c pre =>
        have ht : TailStep M (quiet pre ++ (a, some q) :: quiet post)
            (quiet pre ++ (a', some q') :: quiet post) := .stay pre post q q' a a' htr
        rcases denseScan_before_complete M ht with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.same :: roles, s, by
          simp only [quiet, List.map_cons, List.cons_append, denseScan, List.map_cons,
            scanList, scanSlot, if_pos rfl]
          exact hscan, hs⟩

    | left pre b post q q' a a' htr =>
      cases pre with
      | nil =>
        -- impossible: a genuine left move has a predecessor cell in this constructor
        rcases (denseScan_needLeft_iff M q'
          ((a, some q) :: quiet post) ((a', none) :: quiet post)).mpr
            ⟨a, a', q, post, rfl, rfl, htr⟩ with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.leftDest :: roles, s, by
          simp only [quiet, List.map_nil, List.nil_append, denseScan, List.map_cons,
            scanList, scanSlot, if_pos rfl]
          exact hscan, hs⟩
      | cons c pre =>
        have ht : TailStep M
            (quiet pre ++ (b, none) :: (a, some q) :: quiet post)
            (quiet pre ++ (b, some q') :: (a', none) :: quiet post) :=
          .left pre b post q q' a a' htr
        rcases denseScan_before_complete M ht with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.same :: roles, s, by
          simp only [quiet, List.map_cons, List.cons_append, denseScan, List.map_cons,
            scanList, scanSlot, if_pos rfl]
          exact hscan, hs⟩
    | right pre q q' a a' b post htr =>
      cases pre with
      | nil =>
        rcases (denseScan_needRight_iff M q'
          ((b, none) :: quiet post) ((b, some q') :: quiet post)).mpr
            ⟨b, post, rfl, rfl⟩ with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.rightSource q' :: roles, s, by
          simp only [quiet, List.map_nil, List.nil_append, denseScan, List.map_cons,
            scanList, scanSlot, true_or, if_true, if_pos htr]
          exact hscan, hs⟩
      | cons c pre =>
        have ht : TailStep M
            (quiet pre ++ (a, some q) :: (b, none) :: quiet post)
            (quiet pre ++ (a', none) :: (b, some q') :: quiet post) :=
          .right pre q q' a a' b post htr
        rcases denseScan_before_complete M ht with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.same :: roles, s, by
          simp only [quiet, List.map_cons, List.cons_append, denseScan, List.map_cons,
            scanList, scanSlot, if_pos rfl]
          exact hscan, hs⟩
    | rightClamp pre q q' a a' htr =>
      cases pre with
      | nil =>
        exact ⟨[Role.rightClamp], .rightClampCandidate, by
          simp [quiet, denseScan, scanList, scanSlot, htr], rfl⟩
      | cons c pre =>
        have ht : TailStep M (quiet pre ++ [(a, some q)])
            (quiet pre ++ [(a', some q')]) := .rightClamp pre q q' a a' htr
        rcases denseScan_before_complete M ht with ⟨roles, s, hscan, hs⟩
        exact ⟨Role.same :: roles, s, by
          simp only [quiet, List.map_cons, List.cons_append, denseScan, List.map_cons,
            scanList, scanSlot, if_pos rfl]
          exact hscan, hs⟩

/-! ## Logical rows and actual bounded-tape configurations -/

private def tapeList (t : DLBA.BoundedTape (VSym B Γ) n) : List (VSym B Γ) :=
  List.ofFn t.contents

private lemma tapeList_length (t : DLBA.BoundedTape (VSym B Γ) n) :
    (tapeList t).length = n + 1 := by simp [tapeList]

private lemma tapeList_loadEnd (w : List B) :
    tapeList (B := B) (Γ := Γ) (LBA.loadEnd w) =
      LBA.leftMark :: w.map (fun b => Sum.inl (some (Sum.inl b))) ++ [LBA.rightMark] := by
  let emb : B → LBA.EndAlpha B Γ := fun b => Sum.inl (some (Sum.inl b))
  let tail : List (LBA.EndAlpha B Γ) := w.map emb ++ [LBA.rightMark]
  change tapeList (B := B) (Γ := Γ) (LBA.loadEnd w) = LBA.leftMark :: tail
  apply List.ext_getElem
  · simp [tapeList, tail]
  · intro i hi₁ hi₂
    have hiBound₁ : i ≤ w.length + 1 := by simpa [tail] using hi₂
    have hiBound : i < w.length + 2 := by omega
    simp only [tapeList, List.getElem_ofFn]
    unfold LBA.loadEnd
    simp only
    split
    next hzero =>
      subst i
      rfl
    next hzero =>
      have hi : i = (i - 1) + 1 := by omega
      have hitail : i - 1 < tail.length := by simp [tail]; omega
      rw [show (LBA.leftMark :: tail)[i] = tail[i - 1]'hitail from calc
        (LBA.leftMark :: tail)[i] = (LBA.leftMark :: tail)[(i - 1) + 1] :=
          getElem_congr rfl hi hi₂
        _ = tail[i - 1] := List.getElem_cons_succ LBA.leftMark tail (i - 1)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hitail)]
      unfold tail
      split
      next hmid =>
        rw [List.getElem_append_left (by simpa using hmid)]
        rw [List.getElem_map]
        rfl
      next hmid =>
        rw [List.getElem_append_right]
        · have : i = w.length + 1 := by omega
          subst i
          simp
        · simp only [List.length_map]
          omega

private def cfgView (c : DLBA.Cfg (VSym B Γ) Λ n) : List (VCell B Γ Λ) :=
  quiet ((tapeList c.tape).take c.tape.head.1) ++
    (c.tape.read, some c.state) :: quiet ((tapeList c.tape).drop (c.tape.head.1 + 1))

private def headInfo : List (VCell B Γ Λ) → Option (ℕ × Λ)
  | [] => none
  | (_, some q) :: _ => some (0, q)
  | (_, none) :: xs => (headInfo xs).map fun p => (p.1 + 1, p.2)

@[simp] private lemma headInfo_quiet (xs : List (VSym B Γ)) :
    headInfo (quiet (B := B) (Γ := Γ) (Λ := Λ) xs) = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (headInfo (quiet xs)).map (fun p => (p.1 + 1, p.2)) = none
    rw [ih]
    rfl

private lemma headInfo_quiet_head (pre post : List (VSym B Γ)) (a : VSym B Γ) (q : Λ) :
    headInfo (quiet pre ++ (a, some q) :: quiet post) = some (pre.length, q) := by
  induction pre with
  | nil => simp [quiet, headInfo]
  | cons b pre ih =>
    change (headInfo (quiet pre ++ (a, some q) :: quiet post)).map
      (fun p => (p.1 + 1, p.2)) = some ((b :: pre).length, q)
    rw [ih]
    simp

private lemma map_fst_quiet (xs : List (VSym B Γ)) :
    (quiet (B := B) (Γ := Γ) (Λ := Λ) xs).map Prod.fst = xs := by
  simp [quiet, Function.comp_def]

private lemma cfgView_headInfo (c : DLBA.Cfg (VSym B Γ) Λ n) :
    headInfo (cfgView c) = some (c.tape.head.1, c.state) := by
  unfold cfgView
  rw [headInfo_quiet_head]
  have hb : c.tape.head.1 ≤ (tapeList c.tape).length := by
    rw [tapeList_length]
    exact c.tape.head.isLt.le
  simp [Nat.min_eq_left hb]

private lemma cfgView_map_fst (c : DLBA.Cfg (VSym B Γ) Λ n) :
    (cfgView c).map Prod.fst = tapeList c.tape := by
  unfold cfgView
  simp only [List.map_append, List.map_cons, map_fst_quiet, List.map_nil]
  have hb : c.tape.head.1 < (tapeList c.tape).length := by
    rw [tapeList_length]
    exact c.tape.head.isLt
  have hread : c.tape.read = (tapeList c.tape)[c.tape.head.1]'hb := by
    unfold tapeList DLBA.BoundedTape.read
    symm
    exact List.getElem_ofFn (f := c.tape.contents) (h := hb)
  rw [hread]
  change (tapeList c.tape).take c.tape.head.1 ++
      ([(tapeList c.tape)[c.tape.head.1]] ++
        (tapeList c.tape).drop (c.tape.head.1 + 1)) = tapeList c.tape
  rw [← List.append_assoc]
  rw [List.take_concat_get' (tapeList c.tape) c.tape.head.1 hb]
  exact List.take_append_drop (c.tape.head.1 + 1) (tapeList c.tape)

private lemma cfgView_eq_quiet_head_iff
    (c : DLBA.Cfg (VSym B Γ) Λ n) (pre post : List (VSym B Γ))
    (a : VSym B Γ) (q : Λ)
    (h : cfgView c = quiet pre ++ (a, some q) :: quiet post) :
    pre.length = c.tape.head.1 ∧ q = c.state ∧ tapeList c.tape = pre ++ a :: post := by
  have hh := congrArg headInfo h
  rw [cfgView_headInfo, headInfo_quiet_head] at hh
  injection hh with hpair
  have hlen : pre.length = c.tape.head.1 := congrArg Prod.fst hpair |>.symm
  have hq : q = c.state := congrArg Prod.snd hpair |>.symm
  have hc := congrArg (List.map Prod.fst) h
  rw [cfgView_map_fst] at hc
  simp [quiet, Function.comp_def] at hc
  exact ⟨hlen, hq, hc⟩

private lemma cfgView_decompose
    (c : DLBA.Cfg (VSym B Γ) Λ n) (pre post : List (VSym B Γ))
    (a : VSym B Γ) (q : Λ)
    (h : cfgView c = quiet pre ++ (a, some q) :: quiet post) :
    pre = (tapeList c.tape).take c.tape.head.1 ∧
      post = (tapeList c.tape).drop (c.tape.head.1 + 1) ∧
      a = c.tape.read ∧ q = c.state := by
  rcases cfgView_eq_quiet_head_iff c pre post a q h with ⟨hlen, hq, hc⟩
  have hpre : pre = (tapeList c.tape).take c.tape.head.1 := by
    rw [hc, ← hlen]
    simp
  have hpost : post = (tapeList c.tape).drop (c.tape.head.1 + 1) := by
    rw [hc, ← hlen]
    simp
  have ha : a = c.tape.read := by
    have hbpre : pre.length < (tapeList c.tape).length := by rw [hc]; simp
    have hsym : (tapeList c.tape)[pre.length]'hbpre = a := by
      have ho := congrArg (fun xs => xs[pre.length]?) hc
      change (tapeList c.tape)[pre.length]? = (pre ++ a :: post)[pre.length]? at ho
      rw [List.getElem?_eq_getElem hbpre] at ho
      simp at ho
      exact ho
    have hbhead : c.tape.head.1 < (tapeList c.tape).length := by
      rw [tapeList_length]
      exact c.tape.head.isLt
    have hread : (tapeList c.tape)[c.tape.head.1]'hbhead = c.tape.read := by
      unfold tapeList DLBA.BoundedTape.read
      exact List.getElem_ofFn (f := c.tape.contents) (h := hbhead)
    calc
      a = (tapeList c.tape)[pre.length]'hbpre := hsym.symm
      _ = (tapeList c.tape)[c.tape.head.1]'hbhead := by simpa only [hlen]
      _ = c.tape.read := hread
  exact ⟨hpre, hpost, ha, hq⟩

private lemma tapeList_write [DecidableEq (VSym B Γ)]
    (t : DLBA.BoundedTape (VSym B Γ) n) (a : VSym B Γ) :
    tapeList (t.write a) = (tapeList t).set t.head.1 a := by
  rw [show (tapeList t).set t.head.1 a =
      List.ofFn (fun i : Fin (n + 1) =>
        ((tapeList t).set t.head.1 a)[i.1]'(by
          have := i.isLt
          simp [tapeList]
          omega)) by
    symm
    simpa [tapeList] using List.ofFn_getElem ((tapeList t).set t.head.1 a)]
  unfold tapeList DLBA.BoundedTape.write
  congr 1
  funext i
  rw [List.getElem_set]
  simp only [Function.update_apply]
  by_cases h : t.head = i
  · subst i
    simp
  · have hv : t.head.1 ≠ i.1 := by
      intro hv
      exact h (Fin.ext hv)
    rw [if_neg (Ne.symm h), if_neg hv]
    have hi : i.1 < (List.ofFn t.contents).length := by
      simpa using i.isLt
    exact (List.getElem_ofFn (f := t.contents) (h := hi)).symm

private lemma tapeList_moveHead (t : DLBA.BoundedTape (VSym B Γ) n) (d : DLBA.Dir) :
    tapeList (t.moveHead d) = tapeList t := by
  cases d <;> rfl

private lemma cfgView_write_stay [DecidableEq (VSym B Γ)]
    (c : DLBA.Cfg (VSym B Γ) Λ n) (q' : Λ) (a' : VSym B Γ) :
    cfgView (⟨q', (c.tape.write a').moveHead .stay⟩ :
      DLBA.Cfg (VSym B Γ) Λ n) =
      quiet ((tapeList c.tape).take c.tape.head.1) ++
        (a', some q') :: quiet ((tapeList c.tape).drop (c.tape.head.1 + 1)) := by
  unfold cfgView
  simp only [DLBA.BoundedTape.moveHead]
  rw [tapeList_write]
  have hh : c.tape.head.1 < (tapeList c.tape).length := by
    rw [tapeList_length]
    exact c.tape.head.isLt
  rw [List.set_eq_take_cons_drop a' hh]
  simp only [DLBA.BoundedTape.read, DLBA.BoundedTape.write, Function.update_self]
  have hpre : ((tapeList c.tape).take c.tape.head.1).length = c.tape.head.1 := by
    simp [Nat.min_eq_left hh.le]
  rw [List.take_append_of_le_length (by rw [hpre])]
  simp only [List.take_take, min_self]
  rw [List.drop_append]
  have hz : ((tapeList c.tape).take c.tape.head.1).drop (c.tape.head.1 + 1) = [] :=
    List.drop_eq_nil_iff.mpr (by rw [hpre]; omega)
  rw [hz]
  simp [Nat.min_eq_left hh.le]

private lemma cfgView_write_left [DecidableEq (VSym B Γ)]
    (c : DLBA.Cfg (VSym B Γ) Λ n) (q' : Λ) (a' : VSym B Γ)
    (hpos : 0 < c.tape.head.1) :
    cfgView (⟨q', (c.tape.write a').moveHead .left⟩ :
      DLBA.Cfg (VSym B Γ) Λ n) =
      quiet ((tapeList c.tape).take (c.tape.head.1 - 1)) ++
        ((tapeList c.tape)[c.tape.head.1 - 1]'(by
          rw [tapeList_length]; omega), some q') ::
        (a', none) :: quiet ((tapeList c.tape).drop (c.tape.head.1 + 1)) := by
  unfold cfgView
  rw [tapeList_moveHead, tapeList_write]
  simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hpos]
  have hh : c.tape.head.1 < (tapeList c.tape).length := by
    rw [tapeList_length]; exact c.tape.head.isLt
  rw [List.set_eq_take_cons_drop a' hh]
  simp only [DLBA.BoundedTape.read, DLBA.BoundedTape.write, Function.update_apply]
  have hne : (⟨c.tape.head.1 - 1, by omega⟩ : Fin (n + 1)) ≠ c.tape.head := by
    intro h
    have hv : c.tape.head.1 - 1 = c.tape.head.1 := by
      simpa using congrArg Fin.val h
    omega
  rw [if_neg hne]
  have hpre : ((tapeList c.tape).take c.tape.head.1).length = c.tape.head.1 := by
    simp [Nat.min_eq_left hh.le]
  have hsmall : c.tape.head.1 - 1 < c.tape.head.1 := by omega
  rw [List.take_append_of_le_length (by rw [hpre]; omega)]
  rw [List.take_take]
  simp only [min_eq_left hsmall.le]
  have hbprev : c.tape.head.1 - 1 < (tapeList c.tape).length := by omega
  have hget : c.tape.contents ⟨c.tape.head.1 - 1, by
      simpa [tapeList_length] using hbprev⟩ =
      (tapeList c.tape)[c.tape.head.1 - 1]'hbprev := by
    symm
    exact List.getElem_ofFn (f := c.tape.contents) (h := hbprev)
  rw [hget]
  have htake : (tapeList c.tape).take c.tape.head.1 =
      (tapeList c.tape).take (c.tape.head.1 - 1) ++
        [(tapeList c.tape)[c.tape.head.1 - 1]'(by rw [tapeList_length]; omega)] := by
    have := List.take_concat_get' (tapeList c.tape) (c.tape.head.1 - 1)
      hbprev
    simpa [Nat.sub_add_cancel hpos] using this
  rw [htake]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  congr 1
  simp only [Nat.sub_add_cancel hpos]
  rw [List.drop_append]
  have hprevlen : ((tapeList c.tape).take (c.tape.head.1 - 1)).length =
      c.tape.head.1 - 1 := by simp [Nat.min_eq_left hbprev.le]
  have hz : ((tapeList c.tape).take (c.tape.head.1 - 1)).drop c.tape.head.1 = [] :=
    List.drop_eq_nil_iff.mpr (by rw [hprevlen]; omega)
  rw [hz]
  have hdiff : c.tape.head.1 - (c.tape.head.1 - 1) = 1 := by omega
  rw [hprevlen]
  rw [hdiff]
  simp [quiet]

private lemma cfgView_write_right [DecidableEq (VSym B Γ)]
    (c : DLBA.Cfg (VSym B Γ) Λ n) (q' : Λ) (a' : VSym B Γ)
    (hpos : c.tape.head.1 < n) :
    cfgView (⟨q', (c.tape.write a').moveHead .right⟩ :
      DLBA.Cfg (VSym B Γ) Λ n) =
      quiet ((tapeList c.tape).take c.tape.head.1) ++
        (a', none) ::
        ((tapeList c.tape)[c.tape.head.1 + 1]'(by
          rw [tapeList_length]; omega), some q') ::
        quiet ((tapeList c.tape).drop (c.tape.head.1 + 2)) := by
  unfold cfgView
  rw [tapeList_moveHead, tapeList_write]
  simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hpos]
  have hh : c.tape.head.1 < (tapeList c.tape).length := by
    rw [tapeList_length]; exact c.tape.head.isLt
  have hbnext : c.tape.head.1 + 1 < (tapeList c.tape).length := by
    rw [tapeList_length]; omega
  rw [List.set_eq_take_cons_drop a' hh]
  simp only [DLBA.BoundedTape.read, Function.update_apply]
  have hne : (⟨c.tape.head.1 + 1, by omega⟩ : Fin (n + 1)) ≠ c.tape.head := by
    intro h
    have hv : c.tape.head.1 + 1 = c.tape.head.1 := by simpa using congrArg Fin.val h
    omega
  rw [if_neg hne]
  have hpre : ((tapeList c.tape).take c.tape.head.1).length = c.tape.head.1 := by
    simp [Nat.min_eq_left hh.le]
  have htakeNew : List.take (c.tape.head.1 + 1)
      ((tapeList c.tape).take c.tape.head.1 ++
        a' :: (tapeList c.tape).drop (c.tape.head.1 + 1)) =
      (tapeList c.tape).take c.tape.head.1 ++ [a'] := by
    rw [List.take_append]
    simp [hpre]
  rw [htakeNew]
  simp only [quiet, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append]
  have hnext : c.tape.contents ⟨c.tape.head.1 + 1, by omega⟩ =
      (tapeList c.tape)[c.tape.head.1 + 1]'hbnext := by
    symm
    exact List.getElem_ofFn (f := c.tape.contents) (h := hbnext)
  rw [hnext]
  congr 1
  rw [List.drop_append]
  have hz : ((tapeList c.tape).take c.tape.head.1).drop (c.tape.head.1 + 2) = [] :=
    List.drop_eq_nil_iff.mpr (by rw [hpre]; omega)
  rw [hz]
  rw [hpre]
  have hdiff : c.tape.head.1 + 1 + 1 - c.tape.head.1 = 2 := by omega
  rw [hdiff]
  simp only [List.drop]
  rw [List.drop_drop]
  congr 2 <;> omega

private lemma virtualStep_of_step [DecidableEq (VSym B Γ)]
    (M : LBA.Machine (VSym B Γ) Λ) {n : ℕ}
    {c c' : DLBA.Cfg (VSym B Γ) Λ n} (hstep : LBA.Step M c c') :
    VirtualStep M (cfgView c) (cfgView c') := by
  rcases hstep with ⟨q', a', d, htr, rfl⟩
  cases d with
  | stay =>
    rw [cfgView_write_stay]
    exact VirtualStep.stay
      ((tapeList c.tape).take c.tape.head.1)
      ((tapeList c.tape).drop (c.tape.head.1 + 1))
      c.state q' c.tape.read a' htr
  | left =>
    by_cases hpos : 0 < c.tape.head.1
    · rw [cfgView_write_left c q' a' hpos]
      have hbprev : c.tape.head.1 - 1 < (tapeList c.tape).length := by
        rw [tapeList_length]; omega
      have htake : (tapeList c.tape).take c.tape.head.1 =
          (tapeList c.tape).take (c.tape.head.1 - 1) ++
            [(tapeList c.tape)[c.tape.head.1 - 1]'hbprev] := by
        simpa [Nat.sub_add_cancel hpos] using
          List.take_concat_get' (tapeList c.tape) (c.tape.head.1 - 1) hbprev
      rw [show cfgView c =
          quiet ((tapeList c.tape).take (c.tape.head.1 - 1)) ++
            ((tapeList c.tape)[c.tape.head.1 - 1]'hbprev, none) ::
            (c.tape.read, some c.state) ::
            quiet ((tapeList c.tape).drop (c.tape.head.1 + 1)) by
        unfold cfgView
        have hquiet : quiet (Λ := Λ) ((tapeList c.tape).take c.tape.head.1) =
            quiet (Λ := Λ) ((tapeList c.tape).take (c.tape.head.1 - 1)) ++
              [((tapeList c.tape)[c.tape.head.1 - 1]'hbprev, (none : Option Λ))] := by
          change ((tapeList c.tape).take c.tape.head.1).map
              (fun a => (a, (none : Option Λ))) =
            ((tapeList c.tape).take (c.tape.head.1 - 1)).map
              (fun a => (a, (none : Option Λ))) ++
                [((tapeList c.tape)[c.tape.head.1 - 1]'hbprev, none)]
          simpa only [List.map_append, List.map_cons, List.map_nil] using congrArg
            (List.map fun a => (a, (none : Option Λ))) htake
        calc
          quiet ((tapeList c.tape).take c.tape.head.1) ++
              (c.tape.read, some c.state) :: quiet ((tapeList c.tape).drop (c.tape.head.1 + 1)) =
            (quiet ((tapeList c.tape).take (c.tape.head.1 - 1)) ++
              [((tapeList c.tape)[c.tape.head.1 - 1]'hbprev, none)]) ++
              (c.tape.read, some c.state) :: quiet ((tapeList c.tape).drop (c.tape.head.1 + 1)) :=
                congrArg (fun z => z ++ (c.tape.read, some c.state) ::
                  quiet ((tapeList c.tape).drop (c.tape.head.1 + 1))) hquiet
          _ = _ := by simp [List.append_assoc]]
      exact VirtualStep.left _ _ _ _ _ _ _ htr
    · have hzero : c.tape.head.1 = 0 := by omega
      have hsucc : cfgView
          (⟨q', (c.tape.write a').moveHead .left⟩ : DLBA.Cfg (VSym B Γ) Λ n) =
          (a', some q') :: quiet ((tapeList c.tape).drop 1) := by
        simpa [DLBA.BoundedTape.moveHead, hzero, cfgView, quiet] using
          cfgView_write_stay c q' a'
      rw [hsucc]
      have hold : cfgView c =
          (c.tape.read, some c.state) :: quiet ((tapeList c.tape).drop 1) := by
        simp [cfgView, hzero, quiet]
      rw [hold]
      exact VirtualStep.leftClamp _ _ _ _ _ htr
  | right =>
    by_cases hpos : c.tape.head.1 < n
    · rw [cfgView_write_right c q' a' hpos]
      rw [show cfgView c =
          quiet ((tapeList c.tape).take c.tape.head.1) ++
            (c.tape.read, some c.state) ::
            ((tapeList c.tape)[c.tape.head.1 + 1]'(by
              rw [tapeList_length]; omega), none) ::
            quiet ((tapeList c.tape).drop (c.tape.head.1 + 2)) by
        unfold cfgView
        have hbnext : c.tape.head.1 + 1 < (tapeList c.tape).length := by
          rw [tapeList_length]; omega
        have htail : (tapeList c.tape).drop (c.tape.head.1 + 1) =
            (tapeList c.tape)[c.tape.head.1 + 1]'hbnext ::
              (tapeList c.tape).drop (c.tape.head.1 + 2) := by
          simpa using List.drop_eq_getElem_cons (l := tapeList c.tape) hbnext
        have hquiet : quiet (Λ := Λ) ((tapeList c.tape).drop (c.tape.head.1 + 1)) =
            ((tapeList c.tape)[c.tape.head.1 + 1]'hbnext, (none : Option Λ)) ::
              quiet (Λ := Λ) ((tapeList c.tape).drop (c.tape.head.1 + 2)) := by
          change ((tapeList c.tape).drop (c.tape.head.1 + 1)).map
              (fun a => (a, (none : Option Λ))) =
            ((tapeList c.tape)[c.tape.head.1 + 1]'hbnext, none) ::
              ((tapeList c.tape).drop (c.tape.head.1 + 2)).map
                (fun a => (a, (none : Option Λ)))
          simpa only [List.map_cons] using congrArg
            (List.map fun a => (a, (none : Option Λ))) htail
        exact congrArg (fun z => quiet ((tapeList c.tape).take c.tape.head.1) ++
          (c.tape.read, some c.state) :: z) hquiet]
      exact VirtualStep.right _ _ _ _ _ _ _ htr
    · have hlast : c.tape.head.1 = n := by
        have := c.tape.head.isLt
        omega
      have hsucc : cfgView
          (⟨q', (c.tape.write a').moveHead .right⟩ : DLBA.Cfg (VSym B Γ) Λ n) =
          quiet ((tapeList c.tape).take n) ++ [(a', some q')] := by
        have hd : (c.tape.write a').moveHead .right = (c.tape.write a').moveHead .stay := by
          simp [DLBA.BoundedTape.moveHead, hlast]
        rw [hd, cfgView_write_stay]
        simp only [hlast]
        have hdrop : (tapeList c.tape).drop (n + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr
          rw [tapeList_length]
        rw [hdrop]
        simp [quiet]
      rw [hsucc]
      have hold : cfgView c =
          quiet ((tapeList c.tape).take n) ++ [(c.tape.read, some c.state)] := by
        unfold cfgView
        rw [hlast]
        have hdrop : (tapeList c.tape).drop (n + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr
          rw [tapeList_length]
        rw [hdrop]
        simp [quiet]
      rw [hold]
      exact VirtualStep.rightClamp _ _ _ _ _ htr

private lemma step_of_virtualStep [DecidableEq (VSym B Γ)]
    (M : LBA.Machine (VSym B Γ) Λ) {n : ℕ}
    (c : DLBA.Cfg (VSym B Γ) Λ n) {row : List (VCell B Γ Λ)}
    (hstep : VirtualStep M (cfgView c) row) :
    ∃ c' : DLBA.Cfg (VSym B Γ) Λ n, LBA.Step M c c' ∧ cfgView c' = row := by
  generalize hold : cfgView c = old at hstep
  cases hstep with
  | stay pre post q q' a a' htr =>
    rcases cfgView_decompose c pre post a q hold with ⟨hpre, hpost, ha, hq⟩
    let c' : DLBA.Cfg (VSym B Γ) Λ n := ⟨q', (c.tape.write a').moveHead .stay⟩
    refine ⟨c', ⟨q', a', .stay, ?_, rfl⟩, ?_⟩
    · simpa [ha, hq] using htr
    · unfold c'
      rw [cfgView_write_stay]
      rw [← hpre, ← hpost]
  | leftClamp post q q' a a' htr =>
    rcases cfgView_decompose c [] post a q hold with ⟨hpre, hpost, ha, hq⟩
    have hzero : c.tape.head.1 = 0 := by
      have := congrArg List.length hpre
      simp [tapeList_length] at this
      omega
    let c' : DLBA.Cfg (VSym B Γ) Λ n := ⟨q', (c.tape.write a').moveHead .left⟩
    refine ⟨c', ⟨q', a', .left, ?_, rfl⟩, ?_⟩
    · simpa [ha, hq] using htr
    · unfold c'
      have hd : (c.tape.write a').moveHead .left = (c.tape.write a').moveHead .stay := by
        simp [DLBA.BoundedTape.moveHead, hzero]
      rw [hd, cfgView_write_stay]
      rw [hzero]
      simp only [List.take_zero, quiet, List.map_nil, List.nil_append]
      rw [hzero] at hpost
      rw [← hpost]
  | left pre b post q q' a a' htr =>
    let pref := pre ++ [b]
    have hold' : cfgView c = quiet pref ++ (a, some q) :: quiet post := by
      simpa [pref, quiet, List.map_append, List.append_assoc] using hold
    rcases cfgView_eq_quiet_head_iff c pref post a q hold' with ⟨hlen, hq, hc⟩
    rcases cfgView_decompose c pref post a q hold' with ⟨hpref, hpost, ha, _⟩
    have hpos : 0 < c.tape.head.1 := by simp [pref] at hlen; omega
    have htake : (tapeList c.tape).take (c.tape.head.1 - 1) = pre := by
      rw [← hlen, hc]
      simp [pref]
    have hbprev : c.tape.head.1 - 1 < (tapeList c.tape).length := by
      rw [tapeList_length]; omega
    have hb : (tapeList c.tape)[c.tape.head.1 - 1]'hbprev = b := by
      have hi : pre.length = c.tape.head.1 - 1 := by simp [pref] at hlen; omega
      have hib : pre.length < (tapeList c.tape).length := by omega
      have ho := congrArg (fun xs => xs[pre.length]?) hc
      change (tapeList c.tape)[pre.length]? = (pref ++ a :: post)[pre.length]? at ho
      rw [List.getElem?_eq_getElem hib] at ho
      simp [pref] at ho
      simpa only [hi] using ho
    let c' : DLBA.Cfg (VSym B Γ) Λ n := ⟨q', (c.tape.write a').moveHead .left⟩
    refine ⟨c', ⟨q', a', .left, ?_, rfl⟩, ?_⟩
    · simpa [ha, hq] using htr
    · unfold c'
      rw [cfgView_write_left c q' a' hpos, htake, hb, ← hpost]
  | right pre q q' a a' b post htr =>
    let suff := b :: post
    have hold' : cfgView c = quiet pre ++ (a, some q) :: quiet suff := by
      simpa [suff, quiet] using hold
    rcases cfgView_eq_quiet_head_iff c pre suff a q hold' with ⟨hlen, hq, hc⟩
    rcases cfgView_decompose c pre suff a q hold' with ⟨hpre, hsuff, ha, _⟩
    have hpos : c.tape.head.1 < n := by
      have hcLen := congrArg List.length hc
      rw [tapeList_length] at hcLen
      simp [suff] at hcLen
      omega
    have hpost : (tapeList c.tape).drop (c.tape.head.1 + 2) = post := by
      rw [hc, ← hlen]
      simp [suff]
    have hbnext : c.tape.head.1 + 1 < (tapeList c.tape).length := by
      rw [tapeList_length]; omega
    have hb : (tapeList c.tape)[c.tape.head.1 + 1]'hbnext = b := by
      have ho := congrArg List.head? hsuff
      rw [List.head?_drop] at ho
      simp only [suff, List.head?_cons] at ho
      rw [List.getElem?_eq_getElem hbnext] at ho
      exact Option.some.inj ho.symm
    let c' : DLBA.Cfg (VSym B Γ) Λ n := ⟨q', (c.tape.write a').moveHead .right⟩
    refine ⟨c', ⟨q', a', .right, ?_, rfl⟩, ?_⟩
    · simpa [ha, hq] using htr
    · unfold c'
      rw [cfgView_write_right c q' a' hpos, ← hpre, hb, hpost]
  | rightClamp pre q q' a a' htr =>
    rcases cfgView_eq_quiet_head_iff c pre [] a q hold with ⟨hlen, hq, hc⟩
    rcases cfgView_decompose c pre [] a q hold with ⟨hpre, hpost, ha, _⟩
    have hlast : c.tape.head.1 = n := by
      have hcLen := congrArg List.length hc
      rw [tapeList_length] at hcLen
      simp at hcLen
      omega
    let c' : DLBA.Cfg (VSym B Γ) Λ n := ⟨q', (c.tape.write a').moveHead .right⟩
    refine ⟨c', ⟨q', a', .right, ?_, rfl⟩, ?_⟩
    · simpa [ha, hq] using htr
    · unfold c'
      have hd : (c.tape.write a').moveHead .right = (c.tape.write a').moveHead .stay := by
        simp [DLBA.BoundedTape.moveHead, hlast]
      rw [hd, cfgView_write_stay, ← hpre]
      have hdrop : (tapeList c.tape).drop (c.tape.head.1 + 1) = [] := by
        simpa using hpost.symm
      rw [hdrop]
      simp [quiet]

private lemma virtualReaches_of_reaches [DecidableEq (VSym B Γ)]
    (M : LBA.Machine (VSym B Γ) Λ) {n : ℕ}
    {c c' : DLBA.Cfg (VSym B Γ) Λ n} (h : LBA.Reaches M c c') :
    Relation.ReflTransGen (VirtualStep M) (cfgView c) (cfgView c') := by
  induction h with
  | refl => exact .refl
  | tail hreach hstep ih =>
      exact ih.tail (virtualStep_of_step M hstep)

private lemma reaches_of_virtualReaches [DecidableEq (VSym B Γ)]
    (M : LBA.Machine (VSym B Γ) Λ) {n : ℕ}
    (c : DLBA.Cfg (VSym B Γ) Λ n) {row : List (VCell B Γ Λ)}
    (h : Relation.ReflTransGen (VirtualStep M) (cfgView c) row) :
    ∃ c' : DLBA.Cfg (VSym B Γ) Λ n,
      LBA.Reaches M c c' ∧ cfgView c' = row := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail hreach hstep ih =>
      obtain ⟨d, hcd, hd⟩ := ih
      obtain ⟨e, hde, he⟩ := step_of_virtualStep M d (hd ▸ hstep)
      exact ⟨e, hcd.tail hde, he⟩

/-! ## Fixed-width physical rows -/

private def blockWidth [Fintype A] (h : A → List B) : ℕ :=
  1 + Finset.univ.sup fun a => (h a).length

private lemma length_lt_blockWidth [Fintype A] (h : A → List B) (a : A) :
    (h a).length < blockWidth h := by
  unfold blockWidth
  simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_of_le
    (Finset.le_sup (f := fun x => (h x).length) (Finset.mem_univ a))

private structure Block (B Γ Λ : Type) (W : ℕ) where
  left : Option (VCell B Γ Λ)
  body : Fin W → Option (VCell B Γ Λ)
  right : Option (VCell B Γ Λ)
deriving Fintype, DecidableEq

private inductive RowCell (A B Γ Λ : Type) (W : ℕ) where
  | raw (a : A)
  | sim (b : Block B Γ Λ W)
deriving Fintype, DecidableEq

private def blockSlots (b : Block B Γ Λ W) : List (Option (VCell B Γ Λ)) :=
  b.left :: List.ofFn b.body ++ [b.right]

private def blockOfFn (f : Fin (W + 2) → Option (VCell B Γ Λ)) : Block B Γ Λ W where
  left := f ⟨0, by omega⟩
  body := fun j => f ⟨j.1 + 1, by omega⟩
  right := f ⟨W + 1, by omega⟩

private lemma blockSlots_blockOfFn
    (f : Fin (W + 2) → Option (VCell B Γ Λ)) :
    blockSlots (blockOfFn f) = List.ofFn f := by
  rw [List.ofFn_succ]
  unfold blockSlots blockOfFn
  congr 1
  rw [List.ofFn_succ_last]
  congr 1

private def refillSlots : List (Option α) → List α → List (Option α)
  | [], _ => []
  | none :: xs, ys => none :: refillSlots xs ys
  | some x :: xs, [] => some x :: refillSlots xs []
  | some _ :: xs, y :: ys => some y :: refillSlots xs ys

private lemma refillSlots_props (xs : List (Option α)) (ys : List α)
    (h : ys.length = (xs.filterMap id).length) :
    (refillSlots xs ys).length = xs.length ∧
      (refillSlots xs ys).map Option.isSome = xs.map Option.isSome ∧
      (refillSlots xs ys).filterMap id = ys := by
  induction xs generalizing ys with
  | nil => simp [refillSlots] at h ⊢; exact h
  | cons x xs ih =>
      cases x with
      | none => simpa [refillSlots] using ih ys h
      | some x =>
          cases ys with
          | nil => simp at h
          | cons y ys =>
              simp only [List.filterMap_cons_some (f := id) rfl, List.length_cons,
                Nat.succ.injEq] at h
              simpa [refillSlots] using ih ys h

private lemma exists_refillBlock (b : Block B Γ Λ W) (ys : List (VCell B Γ Λ))
    (h : ys.length = ((blockSlots b).filterMap id).length) :
    ∃ b' : Block B Γ Λ W,
      (blockSlots b').map Option.isSome = (blockSlots b).map Option.isSome ∧
        (blockSlots b').filterMap id = ys := by
  let zs := refillSlots (blockSlots b) ys
  have hp := refillSlots_props (blockSlots b) ys h
  have hzlen : zs.length = W + 2 := by
    rw [hp.1]
    simp [blockSlots]
  let f : Fin (W + 2) → Option (VCell B Γ Λ) :=
    fun i => zs[i.1]'(by rw [hzlen]; exact i.isLt)
  have hf : List.ofFn f = zs := by
    apply List.ext_getElem
    · simpa [hzlen]
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn]
  refine ⟨blockOfFn f, ?_, ?_⟩
  · rw [blockSlots_blockOfFn, hf]
    exact hp.2.1
  · rw [blockSlots_blockOfFn, hf]
    exact hp.2.2

private def logicalCells (row : List (RowCell A B Γ Λ W)) : List (VCell B Γ Λ) :=
  (row.flatMap fun c => match c with
    | .raw _ => []
    | .sim b => (blockSlots b).filterMap id)

private def initialBody [Fintype A] (h : A → List B) (a : A) :
    Fin (blockWidth h) → Option (VCell B Γ Λ) :=
  fun j => (h a)[j.1]?.map fun b => (Sum.inl (some (Sum.inl b)), none)

private def initialBlock [Fintype A] (M : LBA.Machine (VSym B Γ) Λ)
    (h : A → List B) (first last : Bool) (a : A) : Block B Γ Λ (blockWidth h) where
  left := if first then some (LBA.leftMark, some M.initial) else none
  body := initialBody h a
  right := if last then some (LBA.rightMark, none) else none

private lemma filterMap_ofFn_getElem?_map (f : α → β) (l : List α) {n : ℕ}
    (h : l.length ≤ n) :
    (List.ofFn fun i : Fin n => l[i.1]?.map f).filterMap id = l.map f := by
  induction n generalizing l with
  | zero =>
      have : l = [] := by simpa using h
      subst l
      simp
  | succ n ih =>
      cases l with
      | nil =>
          rw [List.ofFn_succ]
          simp only [List.getElem?_nil, Option.map_none, List.map_nil]
          rw [List.filterMap_cons_none (f := id) rfl]
          change (List.ofFn (fun i : Fin n => (([] : List α)[i.1]?).map f)).filterMap id = []
          exact ih (l := []) (by simp)
      | cons a l =>
          rw [List.ofFn_succ]
          change (some (f a) :: List.ofFn (fun i : Fin n => l[i.1]?.map f)).filterMap id =
            f a :: l.map f
          rw [List.filterMap_cons_some (f := id) rfl]
          congr 1
          exact ih (l := l) (by simp at h ⊢; omega)

private lemma initialBlock_cells [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (first last : Bool) (a : A) :
    (blockSlots (initialBlock M h first last a)).filterMap id =
      (if first then [(LBA.leftMark, some M.initial)] else []) ++
        (h a).map (fun b => (Sum.inl (some (Sum.inl b)), none)) ++
        (if last then [(LBA.rightMark, none)] else []) := by
  have hlen : (h a).length ≤ blockWidth h := (length_lt_blockWidth h a).le
  have hbody := filterMap_ofFn_getElem?_map
    (fun b : B => ((Sum.inl (some (Sum.inl b)), none) : VCell B Γ Λ)) (h a) hlen
  cases first <;> cases last <;>
    simpa [blockSlots, initialBlock, initialBody, List.filterMap_append] using hbody

private def initialRowFrom [Fintype A] (M : LBA.Machine (VSym B Γ) Λ)
    (h : A → List B) (first : Bool) :
    List A → List (RowCell A B Γ Λ (blockWidth h))
  | [] => []
  | [a] => [.sim (initialBlock M h first true a)]
  | a :: b :: w =>
      .sim (initialBlock M h first false a) :: initialRowFrom M h false (b :: w)

private def initialRow [Fintype A] (M : LBA.Machine (VSym B Γ) Λ)
    (h : A → List B) (w : List A) : List (RowCell A B Γ Λ (blockWidth h)) :=
  initialRowFrom M h true w

private lemma logicalCells_initialRowFrom [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (first : Bool) (w : List A) (hw : w ≠ []) :
    logicalCells (initialRowFrom M h first w) =
      (if first then [(LBA.leftMark, some M.initial)] else []) ++
        (w.flatMap h).map (fun b => (Sum.inl (some (Sum.inl b)), none)) ++
        [(LBA.rightMark, none)] := by
  induction w generalizing first with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
      cases w with
      | nil =>
          simpa [initialRowFrom, logicalCells] using initialBlock_cells M h first true a
      | cons b w =>
          rw [initialRowFrom]
          change (blockSlots (initialBlock M h first false a)).filterMap id ++
              logicalCells (initialRowFrom M h false (b :: w)) = _
          rw [initialBlock_cells M h first false a]
          rw [ih false (by simp)]
          simp only [List.flatMap_cons, List.map_append, Bool.false_eq_true, if_false,
            List.nil_append]
          simp [List.append_assoc]

private lemma logicalCells_initialRow [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (w : List A) (hw : w ≠ []) :
    logicalCells (initialRow M h w) =
      (LBA.leftMark, some M.initial) ::
        (w.flatMap h).map (fun b => (Sum.inl (some (Sum.inl b)), none)) ++
        [(LBA.rightMark, none)] := by
  simpa [initialRow] using logicalCells_initialRowFrom M h true w hw

private lemma logicalCells_initialRow_eq_cfgView [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (w : List A) (hw : w ≠ []) :
    logicalCells (initialRow M h w) = cfgView (LBA.initCfgEnd M (w.flatMap h)) := by
  rw [logicalCells_initialRow M h w hw]
  unfold cfgView LBA.initCfgEnd
  rw [tapeList_loadEnd]
  simp [quiet, LBA.loadEnd]

private inductive Cert (B Γ Λ : Type) (W : ℕ) where
  | init
  | sim (roles : Fin (W + 2) → Role Λ)
deriving Fintype, DecidableEq

private inductive CheckState (Λ : Type) where
  | start
  | initRest
  | initDone
  | sim (s : ScanState Λ)
  | bad
deriving Fintype, DecidableEq

private def rolesList (r : Fin (W + 2) → Role Λ) : List (Role Λ) := List.ofFn r

private def checkBlock (M : LBA.Machine (VSym B Γ) Λ)
    (s : ScanState Λ) (old new : Block B Γ Λ W)
    (roles : Fin (W + 2) → Role Λ) : ScanState Λ :=
  (scanList M s (blockSlots old) (blockSlots new) (rolesList roles)).getD .bad

/-! The physical verifier scans fixed-width optional slots, whereas `DenseRun` scans only
the occupied logical cells.  The lemmas below are the generic bridge between these views. -/

private lemma scanList_append (M : LBA.Machine (VSym B Γ) Λ)
    (s : ScanState Λ)
    (old₁ old₂ new₁ new₂ : List (Option (VCell B Γ Λ)))
    (roles₁ roles₂ : List (Role Λ))
    (hnew : old₁.length = new₁.length)
    (hroles : old₁.length = roles₁.length) :
    scanList M s (old₁ ++ old₂) (new₁ ++ new₂) (roles₁ ++ roles₂) =
      (scanList M s old₁ new₁ roles₁).bind fun s' =>
        scanList M s' old₂ new₂ roles₂ := by
  induction old₁ generalizing s new₁ roles₁ with
  | nil =>
      have hnewNil : new₁ = [] := List.length_eq_zero_iff.mp (by simpa using hnew.symm)
      have hrolesNil : roles₁ = [] := List.length_eq_zero_iff.mp (by simpa using hroles.symm)
      subst new₁
      subst roles₁
      rfl
  | cons old old₁ ih =>
      cases new₁ with
      | nil => simp at hnew
      | cons new new₁ =>
        cases roles₁ with
        | nil => simp at hroles
        | cons role roles₁ =>
          simp only [List.length_cons, Nat.succ.injEq] at hnew hroles
          simp only [List.cons_append, scanList]
          exact ih (scanSlot M s old new role) new₁ roles₁ hnew hroles

private lemma sparseScan_accept_to_dense
    (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (Option (VCell B Γ Λ))) (s : ScanState Λ)
    (h : ∃ roles q, scanList M s old new roles = some q ∧ scanAccept q = true) :
    old.map Option.isSome = new.map Option.isSome ∧
      ∃ roles q,
        denseScan M s (old.filterMap id) (new.filterMap id) roles = some q ∧
          scanAccept q = true := by
  induction old generalizing new s with
  | nil =>
      rcases h with ⟨roles, q, hscan, hacc⟩
      cases new with
      | nil =>
        cases roles with
        | nil =>
          simp only [scanList] at hscan
          injection hscan with hq
          subst q
          exact ⟨rfl, [], s, by rfl, hacc⟩
        | cons role roles => simp [scanList] at hscan
      | cons new news =>
        cases roles <;> simp [scanList] at hscan
  | cons old olds ih =>
      rcases h with ⟨roles, q, hscan, hacc⟩
      cases new with
      | nil => cases roles <;> simp [scanList] at hscan
      | cons new news =>
        cases roles with
        | nil => simp [scanList] at hscan
        | cons role roles =>
          simp only [scanList] at hscan
          cases old with
          | none =>
            cases new with
            | none =>
              cases role with
              | same =>
                have ht := ih news s ⟨roles, q, by simpa using hscan, hacc⟩
                rcases ht with ⟨hmask, denseRoles, q', hdense, hq'⟩
                exact ⟨by simpa using hmask, denseRoles, q', by simpa [denseScan] using hdense,
                  hq'⟩
              | stay => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | leftClamp => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | leftDest => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | leftSource => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | rightSource q' => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | rightDest => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
              | rightClamp => exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
            | some new =>
              cases role <;>
                exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
          | some old =>
            cases new with
            | none =>
              cases role <;>
                exact (scanList_bad_noaccept M _ _ _ q (by simpa using hscan) hacc).elim
            | some new =>
              have ht := ih news (scanSlot M s (some old) (some new) role)
                ⟨roles, q, hscan, hacc⟩
              rcases ht with ⟨hmask, denseRoles, q', hdense, hq'⟩
              refine ⟨by simpa using hmask, role :: denseRoles, q', ?_, hq'⟩
              simpa [denseScan] using hdense

private lemma denseScan_accept_to_sparse
    (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (Option (VCell B Γ Λ))) (s : ScanState Λ)
    (hmask : old.map Option.isSome = new.map Option.isSome)
    (h : ∃ roles q,
      denseScan M s (old.filterMap id) (new.filterMap id) roles = some q ∧
        scanAccept q = true) :
    ∃ roles q, scanList M s old new roles = some q ∧ scanAccept q = true := by
  induction old generalizing new s with
  | nil =>
      cases new with
      | nil =>
        rcases h with ⟨roles, q, hscan, hacc⟩
        exact ⟨roles, q, by simpa [denseScan] using hscan, hacc⟩
      | cons new news => simp at hmask
  | cons old olds ih =>
      cases new with
      | nil => simp at hmask
      | cons new news =>
        have hmaskTail : olds.map Option.isSome = news.map Option.isSome := by
          simpa using List.cons.inj hmask |>.2
        cases old with
        | none =>
          cases new with
          | none =>
            have ht := ih news s hmaskTail h
            rcases ht with ⟨roles, q, hscan, hacc⟩
            exact ⟨Role.same :: roles, q, by simpa [scanList] using hscan, hacc⟩
          | some new => simp at hmask
        | some old =>
          cases new with
          | none => simp at hmask
          | some new =>
            rcases h with ⟨roles, q, hscan, hacc⟩
            cases roles with
            | nil => simp [denseScan, scanList] at hscan
            | cons role roles =>
              have hdense : denseScan M (scanSlot M s (some old) (some new) role)
                  (olds.filterMap id) (news.filterMap id) roles = some q := by
                simpa [denseScan] using hscan
              have ht := ih news (scanSlot M s (some old) (some new) role) hmaskTail
                ⟨roles, q, hdense, hacc⟩
              rcases ht with ⟨sparseRoles, q', hsparse, hq'⟩
              exact ⟨role :: sparseRoles, q', by simpa [scanList] using hsparse, hq'⟩

private lemma sparseScan_accept_iff_dense
    (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (Option (VCell B Γ Λ))) (s : ScanState Λ) :
    (∃ roles q, scanList M s old new roles = some q ∧ scanAccept q = true) ↔
      old.map Option.isSome = new.map Option.isSome ∧
        ∃ roles q,
          denseScan M s (old.filterMap id) (new.filterMap id) roles = some q ∧
            scanAccept q = true := by
  constructor
  · exact sparseScan_accept_to_dense M old new s
  · rintro ⟨hmask, h⟩
    exact denseScan_accept_to_sparse M old new s hmask h

private def rowStepCell [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq Γ]
    [DecidableEq Λ] (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) :
    CheckState Λ → RowCell A B Γ Λ (blockWidth h) →
      RowCell A B Γ Λ (blockWidth h) → Cert B Γ Λ (blockWidth h) → CheckState Λ
  | .start, .raw a, .sim b, .init =>
      if b = initialBlock M h true true a then .initDone
      else if b = initialBlock M h true false a then .initRest
      else .bad
  | .initRest, .raw a, .sim b, .init =>
      if b = initialBlock M h false true a then .initDone
      else if b = initialBlock M h false false a then .initRest
      else .bad
  | .start, .sim old, .sim new, .sim roles =>
      .sim (checkBlock M .first old new roles)
  | .sim s, .sim old, .sim new, .sim roles =>
      .sim (checkBlock M s old new roles)
  | _, _, _, _ => .bad

private def rowStepDone : CheckState Λ → Bool
  | .initDone => true
  | .sim s => scanAccept s
  | _ => false

private inductive FinalState where
  | good (accepting : Bool)
  | bad
deriving Fintype, DecidableEq

private def blockAccepting (M : LBA.Machine (VSym B Γ) Λ) (b : Block B Γ Λ W) : Bool :=
  (blockSlots b).any fun x => match x with
    | some (_, some q) => M.accept q
    | _ => false

private def finalCell (M : LBA.Machine (VSym B Γ) Λ) :
    FinalState → RowCell A B Γ Λ W → FinalState
  | .good acc, .sim b => .good (acc || blockAccepting M b)
  | _, _ => .bad

private def pullbackRows [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) :
    CertifiedRowSystem A (RowCell A B Γ Λ (blockWidth h))
      (Cert B Γ Λ (blockWidth h)) (CheckState Λ) FinalState where
  inputCell := RowCell.raw
  stepStart := .start
  stepCell := rowStepCell M h
  stepDone := rowStepDone
  finalStart := .good false
  finalCell := finalCell M
  finalDone
    | .good true => true
    | _ => false

private def initState (first : Bool) : CheckState Λ :=
  if first then .start else .initRest

private lemma evalStep_initialRowFrom
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) (first : Bool)
    (w : List A) (hw : w ≠ []) :
    (pullbackRows M h).evalStep (initState first)
      (w.map RowCell.raw) (initialRowFrom M h first w)
      (List.replicate w.length Cert.init) = some .initDone := by
  induction w generalizing first with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    cases w with
    | nil =>
      cases first <;> simp [pullbackRows, CertifiedRowSystem.evalStep, initState,
        initialRowFrom, rowStepCell, initialBlock]
    | cons b w =>
      have hi := ih false (by simp)
      have hfirst : rowStepCell M h (initState first) (.raw a)
          (.sim (initialBlock M h first false a)) .init = .initRest := by
        cases first <;> simp [initState, rowStepCell, initialBlock]
      rw [initialRowFrom, List.map_cons]
      simp only [List.length_cons, List.replicate_succ, CertifiedRowSystem.evalStep]
      change (pullbackRows M h).evalStep
        (rowStepCell M h (initState first) (.raw a)
          (.sim (initialBlock M h first false a)) .init)
        ((b :: w).map RowCell.raw) (initialRowFrom M h false (b :: w))
        (List.replicate (b :: w).length Cert.init) = some .initDone
      rw [hfirst]
      exact hi

private lemma initialRow_rowStep
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (w : List A) (hw : w ≠ []) :
    (pullbackRows M h).RowStep (w.map RowCell.raw) (initialRow M h w) := by
  refine ⟨List.replicate w.length Cert.init, .initDone, ?_, rfl⟩
  simpa [initialRow, initState] using evalStep_initialRowFrom M h true w hw

@[simp] private lemma rowStepCell_bad
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (old new : RowCell A B Γ Λ (blockWidth h))
    (c : Cert B Γ Λ (blockWidth h)) :
    rowStepCell M h .bad old new c = .bad := by
  cases old <;> cases new <;> cases c <;> rfl

private lemma eval_bad_noaccept
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (old new : List (RowCell A B Γ Λ (blockWidth h)))
    (cert : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep .bad old new cert = some q)
    (hdone : rowStepDone q = true) : False := by
  induction old generalizing new cert with
  | nil =>
    cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
    subst q
    simp [rowStepDone] at hdone
  | cons old olds ih =>
    cases new with
    | nil => simp [CertifiedRowSystem.evalStep] at heval
    | cons new news =>
      cases cert with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons c certs =>
        simp only [CertifiedRowSystem.evalStep] at heval
        change (pullbackRows M h).evalStep
          (rowStepCell M h .bad old new c) olds news certs = some q at heval
        rw [rowStepCell_bad] at heval
        exact ih news certs heval

private lemma eval_initDone_cons_noaccept
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (a : A) (old new : List (RowCell A B Γ Λ (blockWidth h)))
    (cert : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep .initDone
      (.raw a :: old) new cert = some q)
    (hdone : rowStepDone q = true) : False := by
  cases new with
  | nil => simp [CertifiedRowSystem.evalStep] at heval
  | cons new news =>
    cases cert with
    | nil => simp [CertifiedRowSystem.evalStep] at heval
    | cons c certs =>
      simp only [CertifiedRowSystem.evalStep] at heval
      change (pullbackRows M h).evalStep
        (rowStepCell M h .initDone (.raw a) new c) old news certs = some q at heval
      have hb : rowStepCell M h .initDone (.raw a) new c = .bad := by
        cases new <;> cases c <;> rfl
      rw [hb] at heval
      exact eval_bad_noaccept M h old news certs q heval hdone

private lemma eval_initialRowFrom_sound
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (first : Bool) (w : List A)
    (row : List (RowCell A B Γ Λ (blockWidth h)))
    (cert : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep (initState first)
      (w.map RowCell.raw) row cert = some q)
    (hdone : rowStepDone q = true) :
    w ≠ [] ∧ row = initialRowFrom M h first w := by
  induction w generalizing first row cert q with
  | nil =>
    cases row <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
    subst q
    cases first <;> simp [initState, rowStepDone] at hdone
  | cons a w ih =>
    refine ⟨by simp, ?_⟩
    cases row with
    | nil => simp [CertifiedRowSystem.evalStep] at heval
    | cons cell rows =>
      cases cert with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons c certs =>
        cases w with
        | nil =>
          cases rows with
          | cons x xs => simp [CertifiedRowSystem.evalStep] at heval
          | nil =>
            cases certs with
            | cons x xs => simp [CertifiedRowSystem.evalStep] at heval
            | nil =>
              simp only [List.map_cons, List.map_nil, CertifiedRowSystem.evalStep] at heval
              injection heval with hq
              subst q
              cases first with
              | false =>
                change rowStepDone (rowStepCell M h .initRest (.raw a) cell c) = true at hdone
                cases cell with
                | raw x => cases c <;> simp [rowStepCell, rowStepDone] at hdone
                | sim block =>
                  cases c with
                  | sim roles => simp [rowStepCell, rowStepDone] at hdone
                  | init =>
                    simp only [rowStepCell] at hdone
                    by_cases hb : block = initialBlock M h false true a
                    · subst block; simp [initialRowFrom]
                    · rw [if_neg hb] at hdone
                      by_cases hm : block = initialBlock M h false false a
                      · rw [if_pos hm] at hdone; simp [rowStepDone] at hdone
                      · rw [if_neg hm] at hdone; simp [rowStepDone] at hdone
              | true =>
                change rowStepDone (rowStepCell M h .start (.raw a) cell c) = true at hdone
                cases cell with
                | raw x => cases c <;> simp [rowStepCell, rowStepDone] at hdone
                | sim block =>
                  cases c with
                  | sim roles => simp [rowStepCell, rowStepDone] at hdone
                  | init =>
                    simp only [rowStepCell] at hdone
                    by_cases hb : block = initialBlock M h true true a
                    · subst block; simp [initialRowFrom]
                    · rw [if_neg hb] at hdone
                      by_cases hm : block = initialBlock M h true false a
                      · rw [if_pos hm] at hdone; simp [rowStepDone] at hdone
                      · rw [if_neg hm] at hdone; simp [rowStepDone] at hdone
        | cons b w =>
          simp only [List.map_cons, CertifiedRowSystem.evalStep] at heval
          cases first with
          | false =>
            change (pullbackRows M h).evalStep
              (rowStepCell M h .initRest (.raw a) cell c)
              ((b :: w).map RowCell.raw) rows certs = some q at heval
            cases cell with
            | raw x =>
              cases c <;> change (pullbackRows M h).evalStep .bad
                  ((b :: w).map RowCell.raw) rows certs = some q at heval
              all_goals exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim
            | sim block =>
              cases c with
              | sim roles =>
                change (pullbackRows M h).evalStep .bad
                  ((b :: w).map RowCell.raw) rows certs = some q at heval
                exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim
              | init =>
                simp only [rowStepCell] at heval
                split at heval
                · exact (eval_initDone_cons_noaccept M h b (w.map RowCell.raw)
                    rows certs q heval hdone).elim
                · split at heval
                  · obtain ⟨_, hr⟩ := ih false rows certs q heval hdone
                    subst rows
                    simp_all [initialRowFrom]
                  · exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim
          | true =>
            change (pullbackRows M h).evalStep
              (rowStepCell M h .start (.raw a) cell c)
              ((b :: w).map RowCell.raw) rows certs = some q at heval
            cases cell with
            | raw x =>
              cases c <;> change (pullbackRows M h).evalStep .bad
                  ((b :: w).map RowCell.raw) rows certs = some q at heval
              all_goals exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim
            | sim block =>
              cases c with
              | sim roles =>
                change (pullbackRows M h).evalStep .bad
                  ((b :: w).map RowCell.raw) rows certs = some q at heval
                exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim
              | init =>
                simp only [rowStepCell] at heval
                split at heval
                · exact (eval_initDone_cons_noaccept M h b (w.map RowCell.raw)
                    rows certs q heval hdone).elim
                · split at heval
                  · obtain ⟨_, hr⟩ := ih false rows certs q heval hdone
                    subst rows
                    simp_all [initialRowFrom]
                  · exact (eval_bad_noaccept M h _ _ _ q heval hdone).elim

private theorem rowStep_raw_iff
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    {w : List A} {row : List (RowCell A B Γ Λ (blockWidth h))} :
    (pullbackRows M h).RowStep (w.map RowCell.raw) row ↔
      w ≠ [] ∧ row = initialRow M h w := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    simpa [initialRow, initState] using
      (eval_initialRowFrom_sound M h true w row cert q heval hdone)
  · rintro ⟨hw, rfl⟩
    exact initialRow_rowStep M h w hw

private def cellAccepting (M : LBA.Machine (VSym B Γ) Λ) (x : VCell B Γ Λ) : Bool :=
  match x.2 with
  | some q => M.accept q
  | none => false

private lemma any_filterMap_id (p : α → Bool) (xs : List (Option α)) :
    (xs.filterMap id).any p = xs.any (fun x => match x with
      | some a => p a
      | none => false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [ih]

private lemma blockAccepting_eq (M : LBA.Machine (VSym B Γ) Λ)
    (b : Block B Γ Λ W) :
    blockAccepting M b = ((blockSlots b).filterMap id).any (cellAccepting M) := by
  rw [any_filterMap_id]
  unfold blockAccepting
  apply congrArg (fun p => (blockSlots b).any p)
  funext x
  cases x with
  | none => rfl
  | some x =>
      rcases x with ⟨a, q⟩
      cases q <;> rfl

private def simRow (bs : List (Block B Γ Λ W)) : List (RowCell A B Γ Λ W) :=
  bs.map RowCell.sim

private def blockMask (bs : List (Block B Γ Λ W)) : List Bool :=
  (bs.flatMap blockSlots).map Option.isSome

private lemma exists_refillBlocks (bs : List (Block B Γ Λ W))
    (ys : List (VCell B Γ Λ))
    (h : ys.length = (logicalCells (simRow (A := A) bs)).length) :
    ∃ bs' : List (Block B Γ Λ W),
      blockMask bs' = blockMask bs ∧ logicalCells (simRow (A := A) bs') = ys := by
  induction bs generalizing ys with
  | nil =>
      have hnil : ys = [] := by simpa [logicalCells, simRow] using h
      subst ys
      exact ⟨[], rfl, rfl⟩
  | cons b bs ih =>
      let xs := (blockSlots b).filterMap id
      let ys₁ := ys.take xs.length
      let ys₂ := ys.drop xs.length
      have hlogical : logicalCells (simRow (A := A) (b :: bs)) =
          xs ++ logicalCells (simRow (A := A) bs) := by rfl
      have hk : xs.length ≤ ys.length := by rw [h, hlogical]; simp
      have hy₁ : ys₁.length = xs.length := by simp [ys₁, Nat.min_eq_left hk]
      have hy₂ : ys₂.length = (logicalCells (simRow (A := A) bs)).length := by
        simp [ys₂, List.length_drop]
        rw [h, hlogical]
        simp
      obtain ⟨b', hbmask, hbcells⟩ := exists_refillBlock b ys₁ (by simpa [xs] using hy₁)
      obtain ⟨bs', hbsmask, hbscells⟩ := ih ys₂ hy₂
      refine ⟨b' :: bs', ?_, ?_⟩
      · simp only [blockMask, List.flatMap_cons, List.map_append]
        unfold blockMask at hbsmask
        rw [hbmask, hbsmask]
      · change (blockSlots b').filterMap id ++
          logicalCells (simRow (A := A) bs') = ys
        rw [hbcells, hbscells]
        exact List.take_append_drop xs.length ys

private lemma evalFinal_sim
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (acc : Bool) (bs : List (Block B Γ Λ (blockWidth h))) :
    (pullbackRows M h).evalFinal (.good acc) (simRow (A := A) bs) =
      .good (acc || (logicalCells (simRow (A := A) bs)).any (cellAccepting M)) := by
  induction bs generalizing acc with
  | nil => simp [CertifiedRowSystem.evalFinal, logicalCells, simRow]
  | cons b bs ih =>
      change (pullbackRows M h).evalFinal (.good (acc || blockAccepting M b))
          (simRow (A := A) bs) = _
      rw [ih]
      rw [show logicalCells (simRow (A := A) (b :: bs)) =
          (blockSlots b).filterMap id ++ logicalCells (simRow (A := A) bs) from rfl]
      simp only [List.any_append, blockAccepting_eq]
      cases acc <;> cases ((blockSlots b).filterMap id).any (cellAccepting M) <;>
        cases (logicalCells (simRow (A := A) bs)).any (cellAccepting M) <;> rfl

private lemma final_sim_iff
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (bs : List (Block B Γ Λ (blockWidth h))) :
    (pullbackRows M h).Final (simRow (A := A) bs) ↔
      (logicalCells (simRow (A := A) bs)).any (cellAccepting M) = true := by
  unfold CertifiedRowSystem.Final
  change (match (pullbackRows M h).evalFinal (.good false) (simRow (A := A) bs) with
      | .good true => true
      | _ => false) = true ↔ _
  rw [evalFinal_sim M h false bs]
  cases (logicalCells (simRow (A := A) bs)).any (cellAccepting M) <;> rfl

private lemma cfgView_any_accepting (M : LBA.Machine (VSym B Γ) Λ)
    (c : DLBA.Cfg (VSym B Γ) Λ n) :
    (cfgView c).any (cellAccepting M) = M.accept c.state := by
  have hquiet (xs : List (VSym B Γ)) :
      (quiet (Λ := Λ) xs).any (cellAccepting M) = false := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simpa [quiet, cellAccepting] using ih
  unfold cfgView
  rw [List.any_append, hquiet]
  simp [cellAccepting, hquiet]

private def simSlots (bs : List (Block B Γ Λ W)) : List (Option (VCell B Γ Λ)) :=
  bs.flatMap blockSlots

private lemma logicalCells_simRow (bs : List (Block B Γ Λ W)) :
    logicalCells (simRow (A := A) bs) = (simSlots bs).filterMap id := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (blockSlots b).filterMap id ++ logicalCells (simRow (A := A) bs) =
        (blockSlots b ++ simSlots bs).filterMap id
      rw [List.filterMap_append, ih]

private lemma scanList_bad_eq (M : LBA.Machine (VSym B Γ) Λ)
    (old new : List (Option (VCell B Γ Λ))) (roles : List (Role Λ)) (q : ScanState Λ)
    (hscan : scanList M .bad old new roles = some q) : q = .bad := by
  induction old generalizing new roles with
  | nil =>
      cases new <;> cases roles <;> simp [scanList] at hscan
      exact hscan.symm
  | cons old olds ih =>
      cases new with
      | nil => simp [scanList] at hscan
      | cons new news =>
        cases roles with
        | nil => simp [scanList] at hscan
        | cons role roles =>
          simp only [scanList, scanSlot_bad] at hscan
          exact ih news roles hscan

@[simp] private lemma checkBlock_bad (M : LBA.Machine (VSym B Γ) Λ)
    (old new : Block B Γ Λ W) (roles : Fin (W + 2) → Role Λ) :
    checkBlock M .bad old new roles = .bad := by
  unfold checkBlock
  cases hscan : scanList M .bad (blockSlots old) (blockSlots new) (rolesList roles) with
  | none => rfl
  | some q => rw [scanList_bad_eq M _ _ _ q hscan]; rfl

private lemma evalStep_bad_noaccept
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (old new : List (RowCell A B Γ Λ (blockWidth h)))
    (certs : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep .bad old new certs = some q) :
    rowStepDone q ≠ true := by
  induction old generalizing new certs with
  | nil =>
      cases new <;> cases certs <;> simp [CertifiedRowSystem.evalStep] at heval
      subst q
      simp [rowStepDone]
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons new news =>
        cases certs with
        | nil => simp [CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          simp only [CertifiedRowSystem.evalStep, pullbackRows, rowStepCell] at heval
          exact ih news certs heval

private lemma evalStep_simBad_noaccept
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds news : List (Block B Γ Λ (blockWidth h)))
    (certs : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep (.sim .bad)
      (simRow (A := A) olds) (simRow (A := A) news) certs = some q) :
    rowStepDone q ≠ true := by
  induction olds generalizing news certs with
  | nil =>
      cases news <;> cases certs <;> simp [simRow, CertifiedRowSystem.evalStep] at heval
      subst q
      simp [rowStepDone, scanAccept]
  | cons old olds ih =>
      cases news with
      | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons new news =>
        cases certs with
        | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          cases cert with
          | init =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell] at heval
              exact evalStep_bad_noaccept M h _ _ _ q heval
          | sim roles =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell, checkBlock_bad] at heval
              exact ih news certs heval

private lemma evalStep_sim_shape
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (s : ScanState Λ) (olds : List (Block B Γ Λ (blockWidth h)))
    (row : List (RowCell A B Γ Λ (blockWidth h)))
    (certs : List (Cert B Γ Λ (blockWidth h))) (q : CheckState Λ)
    (heval : (pullbackRows M h).evalStep (.sim s)
      (simRow (A := A) olds) row certs = some q)
    (hdone : rowStepDone q = true) :
    ∃ news, row = simRow (A := A) news := by
  induction olds generalizing s row certs with
  | nil =>
      cases row with
      | nil =>
        cases certs with
        | nil => exact ⟨[], rfl⟩
        | cons c cs => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons c cs => cases certs <;> simp [simRow, CertifiedRowSystem.evalStep] at heval
  | cons old olds ih =>
      cases row with
      | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons cell rows =>
        cases certs with
        | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          cases cell with
          | raw a =>
              cases cert <;>
                simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                  pullbackRows, rowStepCell] at heval
              all_goals exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
          | sim new =>
              cases cert with
              | init =>
                  simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                    pullbackRows, rowStepCell] at heval
                  exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
              | sim roles =>
                  simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                    pullbackRows, rowStepCell] at heval
                  obtain ⟨news, hrows⟩ := ih (checkBlock M s old new roles)
                    rows certs heval
                  subst rows
                  exact ⟨new :: news, rfl⟩

private lemma rowStep_from_sim_shape_only
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds : List (Block B Γ Λ (blockWidth h)))
    {row : List (RowCell A B Γ Λ (blockWidth h))}
    (hstep : (pullbackRows M h).RowStep (simRow (A := A) olds) row) :
    ∃ news, row = simRow (A := A) news := by
  rcases hstep with ⟨certs, q, heval, hdone⟩
  cases olds with
  | nil =>
      cases row <;> cases certs <;> simp [simRow, CertifiedRowSystem.evalStep] at heval
      subst q
      simp [pullbackRows, rowStepDone] at hdone
  | cons old olds =>
      cases row with
      | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons cell rows =>
        cases certs with
        | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          cases cell with
          | raw a =>
              cases cert <;>
                simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                  pullbackRows, rowStepCell] at heval
              all_goals exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
          | sim new =>
              cases cert with
              | init =>
                  simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                    pullbackRows, rowStepCell] at heval
                  exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
              | sim roles =>
                  simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                    pullbackRows, rowStepCell] at heval
                  obtain ⟨news, hrows⟩ := evalStep_sim_shape M h
                    (checkBlock M .first old new roles) olds rows certs q heval hdone
                  subst rows
                  exact ⟨new :: news, rfl⟩

private lemma evalStep_sim_accept_to_sparse
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds news : List (Block B Γ Λ (blockWidth h)))
    (certs : List (Cert B Γ Λ (blockWidth h))) (s₀ : ScanState Λ)
    (hacc : ∃ q, (pullbackRows M h).evalStep (.sim s₀)
      (simRow (A := A) olds) (simRow (A := A) news) certs = some q ∧
        rowStepDone q = true) :
    ∃ roles q, scanList M s₀ (simSlots olds) (simSlots news) roles = some q ∧
      scanAccept q = true := by
  induction olds generalizing news certs s₀ with
  | nil =>
      rcases hacc with ⟨q, heval, hdone⟩
      cases news with
      | nil =>
        cases certs with
        | nil =>
          have hq : q = .sim s₀ := by
            simpa [simRow, CertifiedRowSystem.evalStep] using heval.symm
          subst q
          exact ⟨[], s₀, rfl, hdone⟩
        | cons cert certs => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons new news => cases certs <;> simp [simRow, CertifiedRowSystem.evalStep] at heval
  | cons old olds ih =>
      rcases hacc with ⟨q, heval, hdone⟩
      cases news with
      | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons new news =>
        cases certs with
        | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          cases cert with
          | init =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell] at heval
              exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
          | sim blockRoles =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell] at heval
              let s₁ := checkBlock M s₀ old new blockRoles
              have htail := ih news certs s₁ ⟨q, heval, hdone⟩
              rcases htail with ⟨tailRoles, q', hscanTail, hq'⟩
              have hs₁ : s₁ ≠ .bad := by
                intro hs
                rw [hs] at hscanTail
                exact scanList_bad_noaccept M _ _ _ q' hscanTail hq'
              have hblock : scanList M s₀ (blockSlots old) (blockSlots new)
                  (rolesList blockRoles) = some s₁ := by
                have hsdef : s₁ = (scanList M s₀ (blockSlots old) (blockSlots new)
                    (rolesList blockRoles)).getD .bad := rfl
                cases hb : scanList M s₀ (blockSlots old) (blockSlots new)
                    (rolesList blockRoles) with
                | none =>
                    simp [hb] at hsdef
                    exact (hs₁ hsdef).elim
                | some t =>
                    simp [hb] at hsdef
                    exact congrArg some hsdef.symm
              refine ⟨rolesList blockRoles ++ tailRoles, q', ?_, hq'⟩
              change scanList M s₀ (blockSlots old ++ simSlots olds)
                (blockSlots new ++ simSlots news) (rolesList blockRoles ++ tailRoles) = some q'
              rw [scanList_append M s₀ (blockSlots old) (simSlots olds)
                (blockSlots new) (simSlots news) (rolesList blockRoles) tailRoles
                (by simp [blockSlots]) (by simp [blockSlots, rolesList]), hblock]
              exact hscanTail

private lemma rowStep_sim_sound
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds news : List (Block B Γ Λ (blockWidth h)))
    (hstep : (pullbackRows M h).RowStep
      (simRow (A := A) olds) (simRow (A := A) news)) :
    VirtualStep M (logicalCells (simRow (A := A) olds))
      (logicalCells (simRow (A := A) news)) := by
  rcases hstep with ⟨certs, q, heval, hdone⟩
  cases olds with
  | nil =>
      cases news with
      | nil =>
        cases certs with
        | nil =>
          have hq : q = .start := by
            simpa [simRow, CertifiedRowSystem.evalStep] using heval.symm
          subst q
          simp [pullbackRows, rowStepDone] at hdone
        | cons cert certs => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons new news => cases certs <;> simp [simRow, CertifiedRowSystem.evalStep] at heval
  | cons old olds =>
      cases news with
      | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
      | cons new news =>
        cases certs with
        | nil => simp [simRow, CertifiedRowSystem.evalStep] at heval
        | cons cert certs =>
          cases cert with
          | init =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell] at heval
              exact (evalStep_bad_noaccept M h _ _ _ q heval hdone).elim
          | sim blockRoles =>
              simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
                pullbackRows, rowStepCell] at heval
              let s₁ := checkBlock M .first old new blockRoles
              have htail := evalStep_sim_accept_to_sparse M h olds news certs s₁
                ⟨q, heval, hdone⟩
              rcases htail with ⟨tailRoles, q', hscanTail, hq'⟩
              have hs₁ : s₁ ≠ .bad := by
                intro hs
                rw [hs] at hscanTail
                exact scanList_bad_noaccept M _ _ _ q' hscanTail hq'
              have hblock : scanList M .first (blockSlots old) (blockSlots new)
                  (rolesList blockRoles) = some s₁ := by
                have hsdef : s₁ = (scanList M .first (blockSlots old) (blockSlots new)
                    (rolesList blockRoles)).getD .bad := rfl
                cases hb : scanList M .first (blockSlots old) (blockSlots new)
                    (rolesList blockRoles) with
                | none =>
                    simp [hb] at hsdef
                    exact (hs₁ hsdef).elim
                | some t =>
                    simp [hb] at hsdef
                    exact congrArg some hsdef.symm
              have hsparse : ∃ roles q, scanList M .first
                  (simSlots (old :: olds)) (simSlots (new :: news)) roles = some q ∧
                    scanAccept q = true := by
                refine ⟨rolesList blockRoles ++ tailRoles, q', ?_, hq'⟩
                change scanList M .first (blockSlots old ++ simSlots olds)
                  (blockSlots new ++ simSlots news) (rolesList blockRoles ++ tailRoles) = some q'
                rw [scanList_append M .first (blockSlots old) (simSlots olds)
                  (blockSlots new) (simSlots news) (rolesList blockRoles) tailRoles
                  (by simp [blockSlots]) (by simp [blockSlots, rolesList]), hblock]
                exact hscanTail
              have hdense := (sparseScan_accept_iff_dense M
                (simSlots (old :: olds)) (simSlots (new :: news)) .first).mp hsparse
              rw [logicalCells_simRow, logicalCells_simRow]
              exact (denseRun_iff_virtualStep M _ _).mp hdense.2

private lemma rowStep_from_sim_shape
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds : List (Block B Γ Λ (blockWidth h)))
    {row : List (RowCell A B Γ Λ (blockWidth h))}
    (hstep : (pullbackRows M h).RowStep (simRow (A := A) olds) row) :
    ∃ news, row = simRow (A := A) news ∧
      VirtualStep M (logicalCells (simRow (A := A) olds))
        (logicalCells (simRow (A := A) news)) := by
  obtain ⟨news, hr⟩ := rowStep_from_sim_shape_only M h olds hstep
  subst row
  exact ⟨news, rfl, rowStep_sim_sound M h olds news hstep⟩

private lemma scanList_lengths (M : LBA.Machine (VSym B Γ) Λ)
    {s q : ScanState Λ} {old new : List (Option (VCell B Γ Λ))}
    {roles : List (Role Λ)} (hscan : scanList M s old new roles = some q) :
    old.length = new.length ∧ old.length = roles.length := by
  induction old generalizing s new roles with
  | nil => cases new <;> cases roles <;> simp [scanList] at hscan ⊢
  | cons old olds ih =>
      cases new with
      | nil => simp [scanList] at hscan
      | cons new news =>
        cases roles with
        | nil => simp [scanList] at hscan
        | cons role roles =>
          simp only [scanList] at hscan
          obtain ⟨h₁, h₂⟩ := ih hscan
          exact ⟨by simpa using congrArg Nat.succ h₁,
            by simpa using congrArg Nat.succ h₂⟩

private def roleVector (rs : List (Role Λ)) : Fin (W + 2) → Role Λ :=
  fun i => rs[i.1]?.getD .same

private lemma rolesList_roleVector (rs : List (Role Λ))
    (h : rs.length = W + 2) : rolesList (roleVector (W := W) rs) = rs := by
  unfold rolesList roleVector
  apply List.ext_getElem
  · simpa [h]
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

private def splitRoles (W : ℕ) : ℕ → List (Role Λ) →
    List (Fin (W + 2) → Role Λ)
  | 0, _ => []
  | n + 1, rs => roleVector (W := W) (rs.take (W + 2)) ::
      splitRoles W n (rs.drop (W + 2))

private lemma splitRoles_length_flatten (W n : ℕ) (rs : List (Role Λ))
    (h : rs.length = n * (W + 2)) :
    (splitRoles W n rs).length = n ∧
      (splitRoles W n rs).flatMap rolesList = rs := by
  induction n generalizing rs with
  | zero =>
      have hrs : rs = [] := by simpa using h
      subst rs
      simp [splitRoles]
  | succ n ih =>
      have hk : W + 2 ≤ rs.length := by rw [h, Nat.succ_mul]; omega
      have htake : (rs.take (W + 2)).length = W + 2 := by
        simp [Nat.min_eq_left hk]
      have hdrop : (rs.drop (W + 2)).length = n * (W + 2) := by
        simp [List.length_drop, h, Nat.succ_mul]
      obtain ⟨hlen, hflat⟩ := ih (rs.drop (W + 2)) hdrop
      constructor
      · simp [splitRoles, hlen]
      · simp only [splitRoles, List.flatMap_cons]
        rw [rolesList_roleVector _ htake, hflat]
        exact List.take_append_drop (W + 2) rs

private lemma evalStep_sim_of_scan
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (s : ScanState Λ) (olds news : List (Block B Γ Λ (blockWidth h)))
    (vecs : List (Fin (blockWidth h + 2) → Role Λ)) (q : ScanState Λ)
    (hnews : olds.length = news.length) (hvecs : olds.length = vecs.length)
    (hscan : scanList M s (simSlots olds) (simSlots news)
      (vecs.flatMap rolesList) = some q) :
    (pullbackRows M h).evalStep (.sim s) (simRow (A := A) olds)
      (simRow (A := A) news) (vecs.map Cert.sim) = some (.sim q) := by
  induction olds generalizing s news vecs with
  | nil =>
      have hn : news = [] := List.length_eq_zero_iff.mp (by simpa using hnews.symm)
      have hv : vecs = [] := List.length_eq_zero_iff.mp (by simpa using hvecs.symm)
      subst news; subst vecs
      simp [simSlots, scanList] at hscan
      subst q
      rfl
  | cons old olds ih =>
      cases news with
      | nil => simp at hnews
      | cons new news =>
        cases vecs with
        | nil => simp at hvecs
        | cons roles vecs =>
          simp only [List.length_cons, Nat.succ.injEq] at hnews hvecs
          change scanList M s (blockSlots old ++ simSlots olds)
              (blockSlots new ++ simSlots news)
              (rolesList roles ++ vecs.flatMap rolesList) = some q at hscan
          rw [scanList_append M s _ _ _ _ _ _ (by simp [blockSlots])
            (by simp [blockSlots, rolesList])] at hscan
          cases hb : scanList M s (blockSlots old) (blockSlots new) (rolesList roles) with
          | none => simp [hb] at hscan
          | some s' =>
            simp [hb] at hscan
            simp only [simRow, List.map_cons, CertifiedRowSystem.evalStep,
              pullbackRows, rowStepCell]
            have hc : checkBlock M s old new roles = s' := by simp [checkBlock, hb]
            rw [hc]
            exact ih s' news vecs hnews hvecs hscan

private lemma rowStep_sim_complete
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (olds news : List (Block B Γ Λ (blockWidth h)))
    (hmask : blockMask news = blockMask olds)
    (hvirt : VirtualStep M (logicalCells (simRow (A := A) olds))
      (logicalCells (simRow (A := A) news))) :
    (pullbackRows M h).RowStep (simRow (A := A) olds) (simRow (A := A) news) := by
  have hdense : DenseRun M (logicalCells (simRow (A := A) olds))
      (logicalCells (simRow (A := A) news)) :=
    (denseRun_iff_virtualStep M _ _).mpr hvirt
  rw [logicalCells_simRow, logicalCells_simRow] at hdense
  have hm : (simSlots olds).map Option.isSome = (simSlots news).map Option.isSome := by
    simpa [blockMask, simSlots] using hmask.symm
  obtain ⟨roles, q, hsparse, hq⟩ :=
    denseScan_accept_to_sparse M (simSlots olds) (simSlots news) .first hm hdense
  have hlens := scanList_lengths M hsparse
  have hslotLen (bs : List (Block B Γ Λ (blockWidth h))) :
      (simSlots bs).length = bs.length * (blockWidth h + 2) := by
    induction bs with
    | nil => simp [simSlots]
    | cons b bs ih =>
        change (blockSlots b ++ simSlots bs).length = Nat.succ bs.length * (blockWidth h + 2)
        rw [List.length_append, ih, Nat.succ_mul]
        simp [blockSlots]
        omega
  have hroleLen : roles.length = olds.length * (blockWidth h + 2) := by
    rw [← hlens.2, hslotLen]
  have hnewsLen : olds.length = news.length := by
    have := hlens.1
    rw [hslotLen, hslotLen] at this
    exact Nat.mul_right_cancel (by omega) this
  obtain ⟨hvecLen, hvecFlat⟩ := splitRoles_length_flatten
    (blockWidth h) olds.length roles hroleLen
  set vecs := splitRoles (blockWidth h) olds.length roles with hvecDef
  have hvecLen' : vecs.length = olds.length := by simpa [hvecDef] using hvecLen
  have hevalSim := evalStep_sim_of_scan M h .first olds news vecs q hnewsLen hvecLen'.symm
    (by rw [hvecDef, hvecFlat]; exact hsparse)
  have holds : olds ≠ [] := by
    have hvnonempty : ∀ {x y}, VirtualStep M x y → x ≠ [] := by
      intro x y hv
      cases hv <;> simp [quiet]
    intro ho
    subst olds
    exact hvnonempty hvirt rfl
  cases olds with
  | nil => exact (holds rfl).elim
  | cons old olds =>
      cases news with
      | nil => simp at hnewsLen
      | cons new news =>
        have hvne : vecs ≠ [] := by
          intro hv
          rw [hv] at hvecLen'
          simp at hvecLen'
        obtain ⟨roles, vecsTail, hvecs⟩ := List.exists_cons_of_ne_nil hvne
        rw [hvecs] at hevalSim
        refine ⟨(Cert.sim roles :: vecsTail.map Cert.sim), .sim q, ?_, hq⟩
        change (pullbackRows M h).evalStep .start
          (simRow (A := A) (old :: olds)) (simRow (A := A) (new :: news))
          (Cert.sim roles :: vecsTail.map Cert.sim) = some (.sim q)
        rw [show (pullbackRows M h).evalStep .start
            (simRow (A := A) (old :: olds)) (simRow (A := A) (new :: news))
            (Cert.sim roles :: vecsTail.map Cert.sim) =
          (pullbackRows M h).evalStep (.sim .first)
            (simRow (A := A) (old :: olds)) (simRow (A := A) (new :: news))
            (Cert.sim roles :: vecsTail.map Cert.sim) from rfl]
        exact hevalSim

private lemma exists_initialBlocksFrom [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (first : Bool) (w : List A) :
    ∃ bs : List (Block B Γ Λ (blockWidth h)),
      initialRowFrom M h first w = simRow (A := A) bs := by
  induction w generalizing first with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
      cases w with
      | nil => exact ⟨[initialBlock M h first true a], rfl⟩
      | cons b w =>
          obtain ⟨bs, hbs⟩ := ih false
          exact ⟨initialBlock M h first false a :: bs, by
            simpa [initialRowFrom, simRow] using congrArg
              (fun xs => RowCell.sim (initialBlock M h first false a) :: xs) hbs⟩

private lemma exists_initialBlocks [Fintype A]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) (w : List A) :
    ∃ bs : List (Block B Γ Λ (blockWidth h)),
      initialRow M h w = simRow (A := A) bs := by
  simpa [initialRow] using exists_initialBlocksFrom M h true w

private lemma virtualStep_length {M : LBA.Machine (VSym B Γ) Λ} {old new}
    (h : VirtualStep M old new) : old.length = new.length := by
  cases h <;> simp [quiet]

private lemma rowReaches_of_virtualReaches
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (bs : List (Block B Γ Λ (blockWidth h))) {target : List (VCell B Γ Λ)}
    (hreach : Relation.ReflTransGen (VirtualStep M)
      (logicalCells (simRow (A := A) bs)) target) :
    ∃ news : List (Block B Γ Λ (blockWidth h)),
      Relation.ReflTransGen (pullbackRows M h).RowStep
          (simRow (A := A) bs) (simRow (A := A) news) ∧
        logicalCells (simRow (A := A) news) = target := by
  induction hreach with
  | refl => exact ⟨bs, .refl, rfl⟩
  | tail hreach hstep ih =>
      obtain ⟨mids, hrows, hlogical⟩ := ih
      rw [← hlogical] at hstep
      have hlen := (virtualStep_length hstep).symm
      obtain ⟨news, hmask, hcells⟩ :=
        exists_refillBlocks (A := A) mids _ hlen
      have hrs := rowStep_sim_complete M h mids news hmask (by simpa [hcells] using hstep)
      exact ⟨news, hrows.tail hrs, hcells⟩

private lemma rowReaches_of_reaches
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (w : List A) (hw : w ≠ []) {c : DLBA.Cfg (VSym B Γ) Λ ((w.flatMap h).length + 1)}
    (hreach : LBA.Reaches M (LBA.initCfgEnd M (w.flatMap h)) c) :
    ∃ bs : List (Block B Γ Λ (blockWidth h)),
      Relation.ReflTransGen (pullbackRows M h).RowStep (initialRow M h w)
          (simRow (A := A) bs) ∧
        logicalCells (simRow (A := A) bs) = cfgView c := by
  obtain ⟨bs₀, hbs₀⟩ := exists_initialBlocks M h w
  have hvreach := virtualReaches_of_reaches M hreach
  rw [← logicalCells_initialRow_eq_cfgView M h w hw, hbs₀] at hvreach
  obtain ⟨bs, hrows, hlogical⟩ := rowReaches_of_virtualReaches M h bs₀ hvreach
  exact ⟨bs, by simpa [hbs₀] using hrows, hlogical⟩

private lemma virtualReaches_of_rowReaches
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B)
    (bs : List (Block B Γ Λ (blockWidth h)))
    {row : List (RowCell A B Γ Λ (blockWidth h))}
    (hreach : Relation.ReflTransGen (pullbackRows M h).RowStep
      (simRow (A := A) bs) row) :
    ∃ news, row = simRow (A := A) news ∧
      Relation.ReflTransGen (VirtualStep M)
        (logicalCells (simRow (A := A) bs))
        (logicalCells (simRow (A := A) news)) := by
  induction hreach with
  | refl => exact ⟨bs, rfl, .refl⟩
  | tail hreach hstep ih =>
      obtain ⟨mids, rfl, hvreach⟩ := ih
      obtain ⟨news, rfl, hv⟩ := rowStep_from_sim_shape M h mids hstep
      exact ⟨news, rfl, hvreach.tail hv⟩

private lemma evalFinal_bad_raw (M : LBA.Machine (VSym B Γ) Λ)
    (w : List A) :
    List.foldl (finalCell (A := A) (W := W) M) .bad
      (w.map (fun a => RowCell.raw (B := B) (Γ := Γ) (Λ := Λ) (W := W) a)) = .bad := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [finalCell] using ih

private theorem mem_rowReachLanguage_iff
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) (w : List A) :
    w ∈ (pullbackRows M h).rowReachLanguage ↔
      w ≠ [] ∧ LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h)) := by
  constructor
  · rintro ⟨hw, row, hreach, hfinal⟩
    refine ⟨hw, ?_⟩
    rcases Relation.ReflTransGen.cases_head hreach with hrefl | ⟨mid, hinit, htail⟩
    · subst row
      cases w with
      | nil => exact (hw rfl).elim
      | cons a w =>
          unfold CertifiedRowSystem.Final CertifiedRowSystem.evalFinal at hfinal
          simp [pullbackRows, finalCell] at hfinal
          have hbad := evalFinal_bad_raw (W := blockWidth h) M w
          rw [hbad] at hfinal
          simp at hfinal
    · have hmid := (rowStep_raw_iff M h).mp hinit
      rw [hmid.2] at htail
      obtain ⟨bs₀, hbs₀⟩ := exists_initialBlocks M h w
      rw [hbs₀] at htail
      obtain ⟨bs, hrow, hvreach⟩ := virtualReaches_of_rowReaches M h bs₀ htail
      subst row
      have haccRows := (final_sim_iff M h bs).mp hfinal
      have hstart := logicalCells_initialRow_eq_cfgView M h w hw
      rw [hbs₀] at hstart
      rw [hstart] at hvreach
      obtain ⟨c, hcfg, hcview⟩ := reaches_of_virtualReaches M
        (LBA.initCfgEnd M (w.flatMap h)) hvreach
      refine ⟨c, hcfg, ?_⟩
      rw [← hcview, cfgView_any_accepting] at haccRows
      exact haccRows
  · rintro ⟨hw, c, hreach, hacc⟩
    obtain ⟨bs, hrows, hlogical⟩ := rowReaches_of_reaches M h w hw hreach
    refine ⟨hw, simRow (A := A) bs, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (initialRow_rowStep M h w hw) hrows
    · apply (final_sim_iff M h bs).mpr
      rw [hlogical, cfgView_any_accepting]
      exact hacc

private theorem rowReachLanguage_eq
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) :
    (pullbackRows M h).rowReachLanguage =
      {w : List A | w ≠ [] ∧ LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h))} := by
  ext w
  exact mem_rowReachLanguage_iff M h w

private theorem inverseMachine_isCS
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Γ] [DecidableEq Γ] [Fintype Λ] [DecidableEq Λ]
    (M : LBA.Machine (VSym B Γ) Λ) (h : A → List B) :
    is_CS {w : List A | LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h))} := by
  let S := pullbackRows M h
  have hpos : is_LBA_pos S.rowReachLanguage :=
    CertifiedRowSystem.is_LBA_pos_rowReachLanguage S
  have hcore : is_CS S.rowReachLanguage := is_LBA_pos_imp_isCS hpos
  rw [show S.rowReachLanguage =
      {w : List A | w ≠ [] ∧ LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h))} by
        exact rowReachLanguage_eq M h] at hcore
  apply is_CS_of_diff_empty_of_is_CS
  convert hcore using 1
  ext w
  change (LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h)) ∧ w ≠ []) ↔
    (w ≠ [] ∧ LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h)))
  tauto

end CSInverseHomomorphism

open CSInverseHomomorphism

/-- Context-sensitive languages over arbitrary finite alphabets are closed under inverse
string homomorphism, including homomorphisms that erase letters. -/
public theorem is_CS_inverseHomomorphicImage
    {A B : Type} [Fintype A] [Fintype B]
    (L : Language B) (h : A → List B) (hL : is_CS L) :
    is_CS {w : List A | w.flatMap h ∈ L} := by
  classical
  have hLBA : is_LBA L := CS_subset_LBA hL
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hLBA
  letI : Fintype Γ := hΓ
  letI : Fintype Λ := hΛ
  letI : DecidableEq Γ := hdΓ
  letI : DecidableEq Λ := hdΛ
  have hpre := inverseMachine_isCS (A := A) M h
  convert hpre using 1
  ext w
  change L (w.flatMap h) ↔ LBA.Accepts M (LBA.initCfgEnd M (w.flatMap h))
  exact Iff.of_eq (congrFun hM (w.flatMap h)).symm

/-- The class of context-sensitive languages is closed under inverse string homomorphism over
all finite source and target alphabet types. -/
public theorem CS_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_CS := by
  intro A B _ _ L h hL
  exact is_CS_inverseHomomorphicImage L h hL

end
