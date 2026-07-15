module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Construction
import Mathlib.Tactic

@[expose]
public section

/-!
# Correctness and uniqueness of the boot transition

The boot scanner has no certificate choices: on a nonempty encoded input row it
accepts exactly the canonical initialized protocol row.
-/

open Classical

namespace CertifiedRowSystem.Complement

private theorem initializedProtocolCell_eq_of_bootLocalOK
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) (input : I) (first : Bool) (new : ProtocolCell A)
    (hlocal : bootLocalOK (inputProtocolCell sourceCell input) new = true)
    (hcount : new.counter.oldCount =
      if first then (countCodec A).one (countRadix_gt_one A)
      else (countCodec A).zero) :
    new = initializedProtocolCell first (sourceCell input) := by
  rcases new with ⟨⟨ns, nd, no, ni, np, nf⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
  cases first <;>
    simp [bootLocalOK, inputProtocolCell, initializedProtocolCell] at hlocal hcount ⊢ <;>
    aesop

private theorem evalBoot_false_ne_done
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (one : RowNumeral.OneState) (old new : ProtocolRow A) :
    evalBoot (.scan one false) old new (List.replicate old.length .boot) ≠
      some (.scan .rest true) := by
  induction old generalizing one new with
  | nil =>
      cases new <;> simp [evalBoot]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalBoot]
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ, evalBoot, bootStepCell,
            Bool.false_and]
          exact ih _ news

private theorem evalBoot_bad_ne_done
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (ok : Bool) (old new : ProtocolRow A) :
    evalBoot (.scan .bad ok) old new (List.replicate old.length .boot) ≠
      some (.scan .rest true) := by
  induction old generalizing ok new with
  | nil =>
      cases new <;> simp [evalBoot]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalBoot]
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ, evalBoot, bootStepCell,
            RowNumeral.DigitCodec.oneStep]
          exact ih _ news

private theorem evalBoot_rest_unique
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) (input : List I) (new : ProtocolRow A)
    (h : evalBoot (.scan .rest true)
      (input.map (inputProtocolCell sourceCell)) new
      (List.replicate input.length .boot) = some (.scan .rest true)) :
    new = input.map (initializedProtocolCell false ∘ sourceCell) := by
  induction input generalizing new with
  | nil =>
      cases new <;> simp [evalBoot] at h ⊢
  | cons input inputs ih =>
      cases new with
      | nil => simp [evalBoot] at h
      | cons new news =>
          by_cases hcount : new.counter.oldCount = (countCodec A).zero
          · by_cases hlocal : bootLocalOK (inputProtocolCell sourceCell input) new = true
            · have htail : evalBoot (.scan .rest true)
                  (inputs.map (inputProtocolCell sourceCell)) news
                  (List.replicate inputs.length .boot) = some (.scan .rest true) := by
                simpa [List.map_cons, List.length_cons, List.replicate_succ,
                  evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
                  hcount, hlocal] using h
              have hhead := initializedProtocolCell_eq_of_bootLocalOK
                sourceCell input false new hlocal (by simpa using hcount)
              simp only [List.map_cons]
              rw [hhead, ih news htail]
              simp [Function.comp_def]
            · have hfalse := evalBoot_false_ne_done (.rest)
                (inputs.map (inputProtocolCell sourceCell)) news
              apply False.elim
              apply hfalse
              simpa [List.map_cons, List.length_cons, List.replicate_succ,
                evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
                hcount, hlocal] using h
          · have hbad := evalBoot_bad_ne_done
                (bootLocalOK (inputProtocolCell sourceCell input) new)
                (inputs.map (inputProtocolCell sourceCell)) news
            apply False.elim
            apply hbad
            simpa [List.map_cons, List.length_cons, List.replicate_succ,
              evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
              hcount] using h

/-- On a nonempty encoded input row, boot acceptance uniquely determines the
canonical initialized row. -/
@[simp] public theorem isBoot_input_iff_eq_initialized
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) {input : List I} (hne : input ≠ [])
    (new : ProtocolRow A) :
    IsBoot (input.map (inputProtocolCell sourceCell)) new ↔
      new = initializedProtocolRow (input.map sourceCell) := by
  constructor
  · rintro ⟨out, heval, hdone⟩
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases new with
    | nil => simp [evalBoot] at heval
    | cons newHead newTail =>
        cases out with
        | start => simp [bootDone] at hdone
        | bad => simp [bootDone] at hdone
        | scan one ok =>
            cases one <;> cases ok <;> simp [bootDone] at hdone
            by_cases hcount : newHead.counter.oldCount =
                (countCodec A).one (countRadix_gt_one A)
            · by_cases hlocal :
                  bootLocalOK (inputProtocolCell sourceCell first) newHead = true
              · have htail : evalBoot (.scan .rest true)
                    (rest.map (inputProtocolCell sourceCell)) newTail
                    (List.replicate rest.length .boot) = some (.scan .rest true) := by
                  simpa [List.map_cons, List.length_cons, List.replicate_succ,
                    evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
                    hcount, hlocal] using heval
                have hhead := initializedProtocolCell_eq_of_bootLocalOK
                  sourceCell first true newHead hlocal (by simpa using hcount)
                simp only [List.map_cons, initializedProtocolRow]
                rw [hhead, evalBoot_rest_unique sourceCell rest newTail htail]
                simp [Function.comp_def, List.map_map]
              · have hfalse := evalBoot_false_ne_done (.rest)
                    (rest.map (inputProtocolCell sourceCell)) newTail
                exact False.elim (hfalse (by
                  simpa [List.map_cons, List.length_cons, List.replicate_succ,
                    evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
                    hcount, hlocal] using heval))
            · have hbad := evalBoot_bad_ne_done
                  (bootLocalOK (inputProtocolCell sourceCell first) newHead)
                  (rest.map (inputProtocolCell sourceCell)) newTail
              exact False.elim (hbad (by
                simpa [List.map_cons, List.length_cons, List.replicate_succ,
                  evalBoot, bootStepCell, RowNumeral.DigitCodec.oneStep,
                  hcount] using heval))
  · rintro rfl
    exact isBoot_input_initialized sourceCell hne

/-- A successful boot from an encoded input establishes the full initialization
invariant. -/
public theorem isInitialized_of_isBoot_input
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) {input : List I} (hne : input ≠ [])
    {new : ProtocolRow A}
    (hboot : IsBoot (input.map (inputProtocolCell sourceCell)) new) :
    IsInitialized (input.map sourceCell) new := by
  rw [(isBoot_input_iff_eq_initialized sourceCell hne new).1 hboot]
  exact isInitialized_initializedProtocolRow (by simpa using hne)

/-- Phase and width projections of a successful boot from an encoded input. -/
public theorem isBoot_input_phases_length
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) {input : List I} (hne : input ≠ [])
    {new : ProtocolRow A}
    (hboot : IsBoot (input.map (inputProtocolCell sourceCell)) new) :
    HasPhase .input (input.map (inputProtocolCell sourceCell)) ∧
      HasPhase .roundStart new ∧
      (input.map (inputProtocolCell sourceCell)).length = new.length := by
  have hinit := isInitialized_of_isBoot_input sourceCell hne hboot
  refine ⟨?_, hinit.2.1, ?_⟩
  · intro cell hcell
    simp only [List.mem_map] at hcell
    obtain ⟨x, _, rfl⟩ := hcell
    rfl
  · have hsourceLength := congrArg List.length hinit.1
    simpa [sourceTrack] using hsourceLength.symm

end CertifiedRowSystem.Complement
