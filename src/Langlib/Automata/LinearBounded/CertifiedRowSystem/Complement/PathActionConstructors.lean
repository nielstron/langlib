module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolSemantics
import Mathlib.Tactic

@[expose]
public section

/-!
# Converse constructors for path-action specifications

`PathActions.lean` projects accepted componentwise scans to track equalities.  The
lemmas here prove the converse direction needed to build canonical accepting runs:
the same track equations imply every cell-local check.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

@[simp]
public theorem scanBits_start_replicate_of_pos (bit : Bool) {n : Nat} (hn : 0 < n) :
    scanBits .start (List.replicate n bit) = .value bit := by
  have htail (k : Nat) :
      scanBits (.value bit) (List.replicate k bit) = .value bit := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, scanBits, UniformScan.step, ih]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [List.replicate_succ, scanBits, UniformScan.step, htail]

@[simp]
public theorem scanPhases_start_replicate_of_pos
    (phase : ProtocolPhase) {n : Nat} (hn : 0 < n) :
    scanPhases .start (List.replicate n phase) = .value phase := by
  have htail (k : Nat) :
      scanPhases (.value phase) (List.replicate k phase) = .value phase := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, scanPhases, UniformScan.step, ih]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [List.replicate_succ, scanPhases, UniformScan.step, htail]

/-- Track equalities characterize the componentwise path-start action exactly. -/
public theorem startsPath_iff_tracks
    (oldPhase newPhase : ProtocolPhase) (old new : ProtocolRow A) :
    StartsPath oldPhase newPhase old new ↔
      old.length = new.length ∧
      HasPhase oldPhase old ∧ HasPhase newPhase new ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      innerTrack new = innerTrack old ∧
      pathTrack new = sourceTrack old ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      seenCountTrack new = seenCountTrack old ∧
      foundTrack new = foundTrack old := by
  constructor
  · exact StartsPath.spec
  · intro h
    induction old generalizing new with
    | nil =>
        cases new <;>
          simp_all [StartsPath, HasPhase, sourceTrack, depthTrack, outerTrack,
            innerTrack, pathTrack, fuelTrack, oldCountTrack, newCountTrack,
            seenCountTrack, foundTrack]
    | cons old olds ih =>
        cases new with
        | nil => simp at h
        | cons new news =>
            rcases old with
              ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
            rcases new with
              ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
            simp only [StartsPath, List.forall₂_cons,
              startPathLocalOK_eq_true_iff]
            simp only [List.length_cons, Nat.succ.injEq, HasPhase, List.mem_cons,
              forall_eq_or_imp, sourceTrack, depthTrack, outerTrack, innerTrack,
              pathTrack, fuelTrack, oldCountTrack, newCountTrack, seenCountTrack,
              foundTrack, List.map_cons, RowNumeral.DigitCodec.zeroRow,
              List.replicate_succ, List.cons.injEq] at h
            rcases h with
              ⟨hlen, holdPhase, hnewPhase, hsource, hdepth, houter, hinner,
                hpath, hfuel, holdCount, hnewCount, hseenCount, hfound⟩
            constructor
            · simp_all
            · simpa only [StartsPath, startPathLocalOK_eq_true_iff] using
                ih news ⟨hlen, holdPhase.2, hnewPhase.2, hsource.2, hdepth.2,
                  houter.2, hinner.2, hpath.2, hfuel.2, holdCount.2,
                  hnewCount.2, hseenCount.2, hfound.2⟩

private theorem pathStepLocal_of_tracks
    (phase : ProtocolPhase) (old new : ProtocolRow A)
    (h : old.length = new.length ∧
      HasPhase phase old ∧ HasPhase phase new ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      innerTrack new = innerTrack old ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      seenCountTrack new = seenCountTrack old ∧
      foundTrack new = foundTrack old) :
    List.Forall₂
      (fun oldCell newCell ↦ pathStepLocalOK phase oldCell newCell = true)
      old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp_all [HasPhase, sourceTrack, depthTrack, outerTrack, innerTrack,
          oldCountTrack, newCountTrack, seenCountTrack, foundTrack]
  | cons old olds ih =>
      cases new with
      | nil => simp at h
      | cons new news =>
          rcases old with
            ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with
            ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          simp only [List.forall₂_cons, pathStepLocalOK_eq_true_iff]
          simp only [List.length_cons, Nat.succ.injEq, HasPhase, List.mem_cons,
            forall_eq_or_imp, sourceTrack, depthTrack, outerTrack, innerTrack,
            oldCountTrack, newCountTrack, seenCountTrack, foundTrack,
            List.map_cons, List.cons.injEq] at h
          rcases h with
            ⟨hlen, holdPhase, hnewPhase, hsource, hdepth, houter, hinner,
              holdCount, hnewCount, hseenCount, hfound⟩
          constructor
          · simp_all
          · simpa only [pathStepLocalOK_eq_true_iff] using
              ih news ⟨hlen, holdPhase.2, hnewPhase.2, hsource.2,
                hdepth.2, houter.2, hinner.2, holdCount.2, hnewCount.2,
                hseenCount.2, hfound.2⟩

/-- Persistent-track equations plus the three global numeral/path checks construct
an accepted path-step action. -/
public theorem isPathStep_of_tracks
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase)
    (old new : ProtocolRow A)
    (htracks : old.length = new.length ∧
      HasPhase phase old ∧ HasPhase phase new ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      innerTrack new = innerTrack old ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      seenCountTrack new = seenCountTrack old ∧
      foundTrack new = foundTrack old)
    (hfuel : (vertexCodec A).evalSucc .carry (fuelTrack old) (fuelTrack new) =
      some .done)
    (hbound : (vertexCodec A).compareRows (fuelTrack old) (depthTrack old) =
      some .lt)
    (hpath : pathTrack new = pathTrack old ∨
      D.RowStep (pathTrack old) (pathTrack new)) :
    IsPathStep D phase old new :=
  ⟨pathStepLocal_of_tracks phase old new htracks, hfuel, hbound, hpath⟩

private theorem finishWitnessLocal_of_tracks
    (old new : ProtocolRow A)
    (h : old.length = new.length ∧ HasPhase .path old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old) :
    List.Forall₂
      (fun oldCell newCell ↦ finishWitnessLocalOK oldCell newCell = true)
      old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp_all [HasPhase, sourceTrack, depthTrack, outerTrack, pathTrack,
          fuelTrack, oldCountTrack, newCountTrack]
  | cons old olds ih =>
      cases new with
      | nil => simp at h
      | cons new news =>
          rcases old with
            ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with
            ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          simp only [List.forall₂_cons, finishWitnessLocalOK_eq_true_iff]
          simp only [List.length_cons, Nat.succ.injEq, HasPhase, List.mem_cons,
            forall_eq_or_imp, sourceTrack, depthTrack, outerTrack, pathTrack,
            fuelTrack, oldCountTrack, newCountTrack, List.map_cons,
            RowNumeral.DigitCodec.zeroRow, List.replicate_succ,
            List.cons.injEq] at h
          rcases h with
            ⟨hlen, holdPhase, hsource, hdepth, houter, hpath, hfuel,
              holdCount, hnewCount⟩
          constructor
          · simp_all
          · simpa only [finishWitnessLocalOK_eq_true_iff] using
              ih news ⟨hlen, holdPhase.2, hsource.2, hdepth.2, houter.2,
                hpath.2, hfuel.2, holdCount.2, hnewCount.2⟩

/-- Construct the exact ordinary witness-completion specification from its track,
successor, uniformity, and source-verifier facts. -/
public theorem isFinishWitness_of_tracks
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A)
    (edgeState : Q) (innerState : RowNumeral.CarryState)
    (oldFound newFound : Bool) (newPhase : ProtocolPhase)
    (holdNe : old ≠ [])
    (htracks : old.length = new.length ∧ HasPhase .path old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old)
    (hedge : D.evalStep D.stepStart (innerTrack old) (outerTrack old)
      (List.replicate old.length ()) = some edgeState)
    (hpath : pathTrack old = innerTrack old)
    (hfuel : fuelTrack old = depthTrack old)
    (hseen : (countCodec A).evalSucc .carry
      (seenCountTrack old) (seenCountTrack new) = some .done)
    (hinner : (vertexCodec A).evalSucc .carry
      (innerTrack old) (innerTrack new) = some innerState)
    (hphase : (innerState = .done ∧ newPhase = .chooseInner) ∨
      (innerState = .carry ∧ newPhase = .finishOuter))
    (holdFound : HasFound oldFound old)
    (hnewFound : HasFound newFound new)
    (hnewPhase : HasPhase newPhase new)
    (hfound : newFound =
      (oldFound || decide (innerTrack old = outerTrack old) ||
        D.stepDone edgeState)) :
    IsFinishWitness D old new := by
  have hnewNe : new ≠ [] := by
    intro hnil
    apply holdNe
    have hlen := htracks.1
    rw [hnil] at hlen
    exact List.length_eq_zero_iff.mp hlen
  have holdScan :
      scanBits .start (old.map (fun cell ↦ cell.found)) = .value oldFound := by
    change scanBits .start (foundTrack old) = .value oldFound
    rw [(foundTrack_eq_replicate_iff old oldFound).2 holdFound]
    exact scanBits_start_replicate_of_pos oldFound (List.length_pos_of_ne_nil holdNe)
  have hnewScan :
      scanBits .start (new.map (fun cell ↦ cell.found)) = .value newFound := by
    change scanBits .start (foundTrack new) = .value newFound
    rw [(foundTrack_eq_replicate_iff new newFound).2 hnewFound]
    exact scanBits_start_replicate_of_pos newFound (List.length_pos_of_ne_nil hnewNe)
  have hphaseScan :
      scanPhases .start (new.map (fun cell ↦ cell.phase)) = .value newPhase := by
    rw [(phaseTrack_eq_replicate_iff new newPhase).2 hnewPhase]
    exact scanPhases_start_replicate_of_pos newPhase (List.length_pos_of_ne_nil hnewNe)
  exact ⟨edgeState, innerState, oldFound, newFound, newPhase,
    finishWitnessLocal_of_tracks old new htracks, hedge, hpath, hfuel, hseen,
    hinner, hphase, holdScan, hnewScan, hphaseScan, hfound⟩

private theorem finalWitnessLocal_of_tracks
    (old new : ProtocolRow A)
    (h : old.length = new.length ∧ HasPhase .finalPath old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      foundTrack new = foundTrack old) :
    List.Forall₂
      (fun oldCell newCell ↦ finalWitnessLocalOK oldCell newCell = true)
      old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp_all [HasPhase, sourceTrack, depthTrack, outerTrack, pathTrack,
          fuelTrack, oldCountTrack, newCountTrack, foundTrack]
  | cons old olds ih =>
      cases new with
      | nil => simp at h
      | cons new news =>
          rcases old with
            ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with
            ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          simp only [List.forall₂_cons, finalWitnessLocalOK_eq_true_iff]
          simp only [List.length_cons, Nat.succ.injEq, HasPhase, List.mem_cons,
            forall_eq_or_imp, sourceTrack, depthTrack, outerTrack, pathTrack,
            fuelTrack, oldCountTrack, newCountTrack, foundTrack, List.map_cons,
            RowNumeral.DigitCodec.zeroRow, List.replicate_succ,
            List.cons.injEq] at h
          rcases h with
            ⟨hlen, holdPhase, hsource, hdepth, houter, hpath, hfuel,
              holdCount, hnewCount, hfound⟩
          constructor
          · simp_all
          · simpa only [finalWitnessLocalOK_eq_true_iff] using
              ih news ⟨hlen, holdPhase.2, hsource.2, hdepth.2, houter.2,
                hpath.2, hfuel.2, holdCount.2, hnewCount.2, hfound.2⟩

/-- Construct the exact final-scan witness-completion specification. -/
public theorem isFinalWitness_of_tracks
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A)
    (finalState : F) (innerState : RowNumeral.CarryState)
    (newPhase : ProtocolPhase) (holdNe : old ≠ [])
    (htracks : old.length = new.length ∧ HasPhase .finalPath old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      foundTrack new = foundTrack old)
    (hfinal : D.evalFinal D.finalStart (innerTrack old) = finalState)
    (hpath : pathTrack old = innerTrack old)
    (hfuel : fuelTrack old = depthTrack old)
    (hseen : (countCodec A).evalSucc .carry
      (seenCountTrack old) (seenCountTrack new) = some .done)
    (hinner : (vertexCodec A).evalSucc .carry
      (innerTrack old) (innerTrack new) = some innerState)
    (hphase : (innerState = .done ∧ newPhase = .finalChoose) ∨
      (innerState = .carry ∧ newPhase = .finalFinish))
    (hnewPhase : HasPhase newPhase new)
    (hfinalDone : D.finalDone finalState = false) :
    IsFinalWitness D old new := by
  have hnewNe : new ≠ [] := by
    intro hnil
    apply holdNe
    have hlen := htracks.1
    rw [hnil] at hlen
    exact List.length_eq_zero_iff.mp hlen
  have hphaseScan :
      scanPhases .start (new.map (fun cell ↦ cell.phase)) = .value newPhase := by
    rw [(phaseTrack_eq_replicate_iff new newPhase).2 hnewPhase]
    exact scanPhases_start_replicate_of_pos newPhase (List.length_pos_of_ne_nil hnewNe)
  exact ⟨finalState, innerState, newPhase,
    finalWitnessLocal_of_tracks old new htracks, hfinal, hpath, hfuel, hseen,
    hinner, hphase, hphaseScan, hfinalDone⟩

end CertifiedRowSystem.Complement
