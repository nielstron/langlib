module

public import Langlib.Automata.LinearBounded.DeterministicSweeping.Definition

import Mathlib.Tactic

@[expose]
public section

/-!
# Every trace of the deterministic sweeping simulator is sweeping

The proof in this file is deliberately independent of the language-simulation invariant.  For
the geometric sweeping property it is enough to remember two much smaller facts:

* during initialization, the first converted cell which the rightward pass can re-read is at
  the physical right endpoint; and
* every installed endpoint flag is sound, and all later writes preserve both flags.

Together with a control-phase/direction invariant, these facts cover every finite trace of the
standard `DLBA.toLBA'` view, including rejecting prefixes and the stationary accepting bridge.
The width-zero case is discharged by the generic fact that every one-cell trace is sweeping.
-/

namespace DLBA

namespace DeterministicSweeping

universe u v w

variable {I : Type u} {Gamma : Type v} {Q : Type w}

/-! ## Endpoint and initialization invariants -/

/-- Every positive endpoint flag stored on the tape names the corresponding physical endpoint.

Only the forward implications are needed: transitions reverse because a flag is `true`.  This
weaker formulation is also preserved while the initialization pass still contains raw cells. -/
private def FlagsSound {n : Nat}
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n) : Prop :=
  forall index cell,
    tape.contents index = workSymbol cell ->
      (cell.left = true -> index.val = 0) /\
      (cell.right = true -> index.val = n)

/-- The unconverted suffix beginning at the current initialization head. -/
private def RawSuffix {n : Nat} (input : Fin (n + 1) -> I)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n) : Prop :=
  forall index, tape.head.val <= index.val ->
    tape.contents index = inputEmbed (input index)

/-- Writing a symbol whose positive flags are sound at the current head preserves global flag
soundness.  Moving the head afterwards is irrelevant because it does not change contents. -/
private lemma flagsSound_writeMove {n : Nat}
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hflags : FlagsSound tape) (written : Alphabet I Gamma Q) (direction : DLBA.Dir)
    (hwritten : forall cell, written = workSymbol cell ->
      (cell.left = true -> tape.head.val = 0) /\
      (cell.right = true -> tape.head.val = n)) :
    FlagsSound ((tape.write written).moveHead direction) := by
  intro index cell hcell
  change (Function.update tape.contents tape.head written) index = workSymbol cell at hcell
  by_cases hindex : index = tape.head
  · subst index
    simpa using hwritten cell (by simpa using hcell)
  · have hold : tape.contents index = workSymbol cell := by
      rw [Function.update_of_ne hindex] at hcell
      exact hcell
    exact hflags index cell hold

/-- Rewriting a converted cell while retaining its endpoint flags preserves flag soundness. -/
private lemma flagsSound_writeMove_preserve {n : Nat}
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hflags : FlagsSound tape) (old new : Cell Gamma Q) (direction : DLBA.Dir)
    (hread : tape.contents tape.head = workSymbol old)
    (hleft : new.left = old.left) (hright : new.right = old.right) :
    FlagsSound ((tape.write (workSymbol new)).moveHead direction) := by
  apply flagsSound_writeMove hflags
  intro cell hcell
  have hnew : cell = new := by simpa using hcell.symm
  subst cell
  have hold := hflags tape.head old hread
  simpa [hleft, hright] using hold

/-- Installing a cell with both flags false is always safe. -/
private lemma flagsSound_writeMove_false {n : Nat}
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hflags : FlagsSound tape) (cell : Cell Gamma Q) (direction : DLBA.Dir)
    (hleft : cell.left = false) (hright : cell.right = false) :
    FlagsSound ((tape.write (workSymbol cell)).moveHead direction) := by
  apply flagsSound_writeMove hflags
  intro other hother
  have hcell : other = cell := by simpa using hother.symm
  subst other
  simp [hleft, hright]

private lemma flagsSound_rawInput {n : Nat} (input : Fin (n + 1) -> I) :
    FlagsSound
      (⟨fun index => inputEmbed (input index), 0⟩ :
        DLBA.BoundedTape (Alphabet I Gamma Q) n) := by
  intro index cell hcell
  simp [inputEmbed, workSymbol] at hcell

/-- A right move after converting the current raw cell leaves the new head at the beginning of
an unconverted suffix. -/
private lemma rawSuffix_writeMove_right {n : Nat}
    (input : Fin (n + 1) -> I)
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hsuffix : RawSuffix input tape) (written : Alphabet I Gamma Q)
    (hhead : tape.head.val < n) :
    RawSuffix input ((tape.write written).moveHead .right) := by
  intro index hindex
  have hne : index ≠ tape.head := by
    intro heq
    subst index
    simp [DLBA.BoundedTape.moveHead, hhead] at hindex
  change (Function.update tape.contents tape.head written) index = inputEmbed (input index)
  rw [Function.update_of_ne hne]
  apply hsuffix index
  simp [DLBA.BoundedTape.moveHead, hhead] at hindex
  omega

private lemma rawSuffix_rawInput {n : Nat} (input : Fin (n + 1) -> I) :
    RawSuffix input
      (⟨fun index => inputEmbed (input index), 0⟩ :
        DLBA.BoundedTape (Alphabet I Gamma Q) n) := by
  intro index _
  rfl

/-- A converted initialization cell with both flags false is sound. -/
private lemma flagsSound_initSweepRaw {n : Nat}
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hflags : FlagsSound tape) (input : I) (embed : I -> Gamma)
    (direction : DLBA.Dir) :
    FlagsSound
      ((tape.write
        (workSymbol (I := I) ⟨false, false, embed input, .plain⟩)).moveHead direction) := by
  apply flagsSound_writeMove_false hflags <;> rfl

/-- Marking the current cell as the right endpoint is sound when the initialization sentinel is
known to be at that endpoint. -/
private lemma flagsSound_markRight {n : Nat}
    {tape : DLBA.BoundedTape (Alphabet I Gamma Q) n}
    (hflags : FlagsSound tape) (cell : Cell Gamma Q)
    (hread : tape.contents tape.head = workSymbol (I := I) cell)
    (hhead : tape.head.val = n) :
    FlagsSound
      ((tape.write (workSymbol (I := I) { cell with right := true })).moveHead .left) := by
  apply flagsSound_writeMove hflags
  intro written hwritten
  have hwritten' : written = { cell with right := true } := by
    simpa using hwritten.symm
  subst written
  constructor
  · intro hleft
    exact (hflags tape.head cell hread).1 hleft
  · intro _
    exact hhead

/-- The phase-indexed invariant needed for the sweeping proof of the `toLBA'` trace.

The first three constructors describe initialization.  Once initialization has turned around,
only `FlagsSound` and exclusion of the two initialization phases are needed.  The final
constructor is the stationary accepting state introduced by `DLBA.toLBA'`. -/
private inductive SoundClaim (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I) :
    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n -> Prop
  | initFirst :
      SoundClaim M embed input
        <| ⟨some .initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩
  | initSweepRaw (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
      (hpositive : 0 < tape.head.val)
      (hsuffix : RawSuffix input tape)
      (hflags : FlagsSound tape) :
      SoundClaim M embed input ⟨some .initSweep, tape⟩
  | initSweepEnd (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
      (hhead : tape.head.val = n)
      (cell : Cell Gamma Q) (hread : tape.contents tape.head = workSymbol cell)
      (hflags : FlagsSound tape) :
      SoundClaim M embed input ⟨some .initSweep, tape⟩
  | running (phase : Phase Q) (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
      (hfirst : phase ≠ .initFirst) (hsweep : phase ≠ .initSweep)
      (hflags : FlagsSound tape) :
      SoundClaim M embed input ⟨some phase, tape⟩
  | terminal (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
      (hflags : FlagsSound tape) :
      SoundClaim M embed input ⟨none, tape⟩

/-- Every actual simulator step after initialization preserves sound endpoint flags. -/
private lemma flagsSound_running_step (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (phase : Phase Q)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hfirst : phase ≠ .initFirst) (hsweep : phase ≠ .initSweep)
    (hflags : FlagsSound tape)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨phase, tape⟩ = some target) :
    FlagsSound target.tape := by
  cases phase with
  | initFirst => exact (hfirst rfl).elim
  | initSweep => exact (hsweep rfl).elim
  | initBack =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hleft : cell.left <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, hleft] at hstep
              · subst target
                exact flagsSound_writeMove_preserve hflags cell cell .left hread rfl rfl
              · subst target
                exact flagsSound_writeMove_preserve hflags cell cell .stay hread rfl rfl
  | scanRight =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases htag : cell.tag with
              | plain =>
                  cases hright : cell.right <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, htag,
                      hright] at hstep
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .right hread rfl rfl
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .left hread rfl rfl
              | head state =>
                  simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, htag] at hstep
                  subst target
                  exact flagsSound_writeMove_preserve hflags cell cell .stay hread rfl rfl
              | needLeft state =>
                  cases hright : cell.right <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, htag,
                      hright] at hstep
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .right hread rfl rfl
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .left hread rfl rfl
  | query state =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hsource : M.transition state cell.symbol with
              | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, hsource] at hstep
              | some move =>
                  rcases move with ⟨next, symbol, direction⟩
                  cases direction with
                  | stay =>
                      cases hright : cell.right <;>
                        simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, hsource,
                          hright] at hstep
                      · subst target
                        simpa [Cell.writeTagged, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.head next)) .right hread rfl rfl)
                      · subst target
                        simpa [Cell.writeTagged, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.head next)) .left hread rfl rfl)
                  | right =>
                      cases hright : cell.right <;>
                        simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, hsource,
                          hright] at hstep
                      · subst target
                        simpa [Cell.writeTagged, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol .plain) .right hread rfl rfl)
                      · subst target
                        simpa [Cell.writeTagged, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.head next)) .left hread rfl rfl)
                  | left =>
                      cases hleft : cell.left <;>
                        cases hright : cell.right <;>
                          simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, hsource,
                            hleft, hright] at hstep
                      · subst target
                        simpa [Cell.writeTagged, hleft, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.needLeft next)) .right hread rfl rfl)
                      · subst target
                        simpa [Cell.writeTagged, hleft, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol .plain) .left hread rfl rfl)
                      · subst target
                        simpa [Cell.writeTagged, hleft, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.head next)) .right hread rfl rfl)
                      · subst target
                        simpa [Cell.writeTagged, hleft, hright] using
                          (flagsSound_writeMove_preserve hflags cell
                            (cell.writeTagged symbol (.head next)) .left hread rfl rfl)
  | putRight state =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hright : cell.right <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueRight, hread, hright] at hstep
              · subst target
                simpa [Cell.withTag, hright] using
                  (flagsSound_writeMove_preserve hflags cell
                    (cell.withTag (.head state)) .right hread rfl rfl)
              · subst target
                simpa [Cell.withTag, hright] using
                  (flagsSound_writeMove_preserve hflags cell
                    (cell.withTag (.head state)) .left hread rfl rfl)
  | scanLeft =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases htag : cell.tag with
              | needLeft state =>
                  simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, htag] at hstep
                  subst target
                  exact flagsSound_writeMove_preserve hflags cell
                    (cell.withTag .plain) .left hread rfl rfl
              | plain =>
                  cases hleft : cell.left <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueLeft, hread, htag,
                      hleft] at hstep
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .left hread rfl rfl
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .stay hread rfl rfl
              | head state =>
                  cases hleft : cell.left <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueLeft, hread, htag,
                      hleft] at hstep
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .left hread rfl rfl
                  · subst target
                    exact flagsSound_writeMove_preserve hflags cell cell .stay hread rfl rfl
  | putLeft state =>
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hleft : cell.left <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, continueLeft, hread, hleft] at hstep
              · subst target
                simpa [Cell.withTag, hleft] using
                  (flagsSound_writeMove_preserve hflags cell
                    (cell.withTag (.head state)) .left hread rfl rfl)
              · subst target
                simpa [Cell.withTag, hleft] using
                  (flagsSound_writeMove_preserve hflags cell
                    (cell.withTag (.head state)) .stay hread rfl rfl)

private lemma running_step_phase_ne_init (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (phase : Phase Q)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hfirst : phase ≠ .initFirst) (hsweep : phase ≠ .initSweep)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨phase, tape⟩ = some target) :
    target.state ≠ .initFirst ∧ target.state ≠ .initSweep := by
  unfold DLBA.step at hstep
  simp only [machine_transition] at hstep
  cases htransition : transition M embed phase (tape.contents tape.head) with
  | none => simp [htransition] at hstep
  | some move =>
      rcases move with ⟨next, written, direction⟩
      simp [htransition] at hstep
      obtain rfl := hstep
      cases hobserved : tape.contents tape.head with
      | none =>
          cases phase <;> simp_all [transition]
      | some observed =>
          cases observed with
          | inl input =>
              cases phase <;> simp_all [transition]
          | inr cell =>
              cases phase with
              | initFirst => exact (hfirst rfl).elim
              | initSweep => exact (hsweep rfl).elim
              | initBack =>
                  cases hleft : cell.left <;>
                    simp_all [transition] <;> aesop
              | scanRight =>
                  cases htag : cell.tag with
                  | head state => simp_all [transition]; aesop
                  | plain =>
                      cases hright : cell.right <;>
                        simp_all [transition, continueRight] <;> aesop
                  | needLeft state =>
                      cases hright : cell.right <;>
                        simp_all [transition, continueRight] <;> aesop
              | query state =>
                  cases hsource : M.transition state cell.symbol with
                  | none => simp_all [transition]
                  | some move =>
                      rcases move with ⟨sourceNext, sourceWritten, sourceDirection⟩
                      cases sourceDirection with
                      | stay =>
                          cases hright : cell.right <;>
                            simp_all [transition, continueRight] <;> aesop
                      | right =>
                          cases hright : cell.right <;>
                            simp_all [transition, continueRight] <;> aesop
                      | left =>
                          cases hleft : cell.left <;>
                            cases hright : cell.right <;>
                              simp_all [transition, continueRight] <;> aesop
              | putRight state =>
                  cases hright : cell.right <;>
                    simp_all [transition, continueRight] <;> aesop
              | scanLeft =>
                  cases htag : cell.tag with
                  | needLeft state => simp_all [transition]; aesop
                  | plain =>
                      cases hleft : cell.left <;>
                        simp_all [transition, continueLeft] <;> aesop
                  | head state =>
                      cases hleft : cell.left <;>
                        simp_all [transition, continueLeft] <;> aesop
              | putLeft state =>
                  cases hleft : cell.left <;>
                    simp_all [transition, continueLeft] <;> aesop

/-! ### Preservation of the initialization invariant -/

private lemma sound_initFirst_step (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed)
      ⟨.initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩ = some target) :
    SoundClaim M embed input ⟨some target.state, target.tape⟩ := by
  let tape : DLBA.BoundedTape (Alphabet I Gamma Q) n :=
    ⟨fun index => inputEmbed (input index), 0⟩
  let cell : Cell Gamma Q :=
    ⟨true, false, embed (input 0), .head M.initial⟩
  have htarget : target =
      ⟨.initSweep, (tape.write (workSymbol (I := I) cell)).moveHead .right⟩ := by
    simpa [DLBA.step, DLBA.BoundedTape.read, machine, transition, tape, cell] using hstep.symm
  subst target
  have hflags : FlagsSound
      ((tape.write (workSymbol (I := I) cell)).moveHead .right) := by
    apply flagsSound_writeMove (flagsSound_rawInput input)
    intro other hother
    have hother' : other = cell := by simpa using hother.symm
    subst other
    simp [cell]
  by_cases hn : n = 0
  · subst n
    apply SoundClaim.initSweepEnd _ _ _ _ hflags
    · simp [tape, DLBA.BoundedTape.moveHead]
    · exact cell
    · simp [tape, cell, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead, workSymbol]
  · apply SoundClaim.initSweepRaw _ _ _ hflags
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [tape, DLBA.BoundedTape.moveHead, hpos]
    · apply rawSuffix_writeMove_right input (rawSuffix_rawInput input)
      simpa [tape] using (show (0 : Nat) < n from Nat.pos_of_ne_zero hn)

private lemma sound_initSweepRaw_step (M : DLBA.Machine Gamma Q)
    (embed : I -> Gamma) {n : Nat} (input : Fin (n + 1) -> I)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hsuffix : RawSuffix input tape)
    (hflags : FlagsSound tape)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨.initSweep, tape⟩ = some target) :
    SoundClaim M embed input ⟨some target.state, target.tape⟩ := by
  have hread : tape.contents tape.head = inputEmbed (input tape.head) :=
    hsuffix tape.head (by omega)
  let cell : Cell Gamma Q :=
    ⟨false, false, embed (input tape.head), .plain⟩
  have htarget : target =
      ⟨.initSweep, (tape.write (workSymbol (I := I) cell)).moveHead .right⟩ := by
    simpa [DLBA.step, DLBA.BoundedTape.read, machine, transition, inputEmbed,
      hread, cell] using hstep.symm
  subst target
  have hflags' : FlagsSound
      ((tape.write (workSymbol (I := I) cell)).moveHead .right) :=
    flagsSound_initSweepRaw hflags (input tape.head) embed .right
  by_cases hhead : tape.head.val < n
  · apply SoundClaim.initSweepRaw _ _ _ hflags'
    · simp [DLBA.BoundedTape.moveHead, hhead]
    · exact rawSuffix_writeMove_right input hsuffix _ hhead
  · have heq : tape.head.val = n := by
      have := tape.head.isLt
      omega
    apply SoundClaim.initSweepEnd _ _ cell _ hflags'
    · simp [DLBA.BoundedTape.moveHead, heq]
    · simp [DLBA.BoundedTape.moveHead, hhead, DLBA.BoundedTape.write,
        cell, workSymbol]

private lemma sound_initSweepEnd_step (M : DLBA.Machine Gamma Q)
    (embed : I -> Gamma) {n : Nat} (input : Fin (n + 1) -> I)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hhead : tape.head.val = n) (cell : Cell Gamma Q)
    (hread : tape.contents tape.head = workSymbol (I := I) cell)
    (hflags : FlagsSound tape)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨.initSweep, tape⟩ = some target) :
    SoundClaim M embed input ⟨some target.state, target.tape⟩ := by
  have htarget : target =
      ⟨.initBack,
        (tape.write (workSymbol (I := I) { cell with right := true })).moveHead .left⟩ := by
    simpa [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] using hstep.symm
  subst target
  exact SoundClaim.running .initBack _ (by simp) (by simp)
    (flagsSound_markRight hflags cell hread hhead)

/-- The geometric invariant is preserved by every concrete step of the standard LBA view.
The second `toLBA'` case is precisely its stationary accepting bridge. -/
private lemma SoundClaim.next [DecidableEq (Alphabet I Gamma Q)]
    (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I)
    {source target : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n}
    (hsource : SoundClaim M embed input source)
    (hstep : LBA.Step (DLBA.toLBA' (machine M embed)) source target) :
    SoundClaim M embed input target := by
  cases hsource with
  | initFirst =>
      rcases DLBA.toLBA'_step_cases (machine M embed) .initFirst _ target hstep with
        hactual | hhalt
      · obtain ⟨phase, tape, rfl, hmachine⟩ := hactual
        exact sound_initFirst_step M embed input hmachine
      · rcases hhalt with ⟨rfl, _, haccept⟩
        simp at haccept
  | initSweepRaw tape hpositive hsuffix hflags =>
      rcases DLBA.toLBA'_step_cases (machine M embed) .initSweep tape target hstep with
        hactual | hhalt
      · obtain ⟨phase, targetTape, rfl, hmachine⟩ := hactual
        exact sound_initSweepRaw_step M embed input tape hsuffix hflags hmachine
      · rcases hhalt with ⟨rfl, _, haccept⟩
        simp at haccept
  | initSweepEnd tape hhead cell hread hflags =>
      rcases DLBA.toLBA'_step_cases (machine M embed) .initSweep tape target hstep with
        hactual | hhalt
      · obtain ⟨phase, targetTape, rfl, hmachine⟩ := hactual
        exact sound_initSweepEnd_step M embed input tape hhead cell hread hflags hmachine
      · rcases hhalt with ⟨rfl, _, haccept⟩
        simp at haccept
  | running phase tape hfirst hsweep hflags =>
      rcases DLBA.toLBA'_step_cases (machine M embed) phase tape target hstep with
        hactual | hhalt
      · obtain ⟨next, targetTape, rfl, hmachine⟩ := hactual
        have hnext := running_step_phase_ne_init M embed phase tape
          hfirst hsweep hmachine
        exact SoundClaim.running next targetTape hnext.1 hnext.2
          (flagsSound_running_step M embed phase tape hfirst hsweep hflags hmachine)
      · rcases hhalt with ⟨rfl, _, _⟩
        exact SoundClaim.terminal tape hflags
  | terminal tape hflags =>
      obtain ⟨next, written, direction, hmem, _⟩ := hstep
      simp [DLBA.toLBA'] at hmem

/-! ## Elementary physical-direction lemmas -/

private lemma physicalDirection_write_moveHead_stay
    {Gamma0 State0 : Type*} {n : Nat}
    (cfg : DLBA.Cfg Gamma0 State0 n) (state : State0) (symbol : Gamma0) :
    LBA.HeadTurns.physicalDirection cfg
      ⟨state, (cfg.tape.write symbol).moveHead .stay⟩ = none := by
  simp [LBA.HeadTurns.physicalDirection, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]

private lemma physicalDirection_write_moveHead_right_of_lt
    {Gamma0 State0 : Type*} {n : Nat}
    (cfg : DLBA.Cfg Gamma0 State0 n) (state : State0) (symbol : Gamma0)
    (hhead : cfg.tape.head.val < n) :
    LBA.HeadTurns.physicalDirection cfg
      ⟨state, (cfg.tape.write symbol).moveHead .right⟩ = some .right := by
  simp [LBA.HeadTurns.physicalDirection, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead, hhead]

private lemma physicalDirection_write_moveHead_right_of_not_lt
    {Gamma0 State0 : Type*} {n : Nat}
    (cfg : DLBA.Cfg Gamma0 State0 n) (state : State0) (symbol : Gamma0)
    (hhead : ¬ cfg.tape.head.val < n) :
    LBA.HeadTurns.physicalDirection cfg
      ⟨state, (cfg.tape.write symbol).moveHead .right⟩ = none := by
  simp [LBA.HeadTurns.physicalDirection, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead, hhead]

private lemma physicalDirection_write_moveHead_left_of_pos
    {Gamma0 State0 : Type*} {n : Nat}
    (cfg : DLBA.Cfg Gamma0 State0 n) (state : State0) (symbol : Gamma0)
    (hhead : 0 < cfg.tape.head.val) :
    LBA.HeadTurns.physicalDirection cfg
      ⟨state, (cfg.tape.write symbol).moveHead .left⟩ = some .left := by
  simp [LBA.HeadTurns.physicalDirection, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead, hhead]

private lemma physicalDirection_write_moveHead_left_of_not_pos
    {Gamma0 State0 : Type*} {n : Nat}
    (cfg : DLBA.Cfg Gamma0 State0 n) (state : State0) (symbol : Gamma0)
    (hhead : ¬ 0 < cfg.tape.head.val) :
    LBA.HeadTurns.physicalDirection cfg
      ⟨state, (cfg.tape.write symbol).moveHead .left⟩ = none := by
  simp [LBA.HeadTurns.physicalDirection, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead, hhead]

/-! ## Phase and remembered-direction compatibility -/

private def RightCompatible {n : Nat}
    (cfg : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (previous : Option LBA.HeadTurns.Direction) : Prop :=
  previous = none ∨ previous = some .right ∨
    (previous = some .left ∧ cfg.tape.head.val = 0)

private def LeftCompatible {n : Nat}
    (cfg : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (previous : Option LBA.HeadTurns.Direction) : Prop :=
  previous = none ∨ previous = some .left ∨
    (previous = some .right ∧ cfg.tape.head.val = n)

/-- The genuine direction which may precede each reachable simulator phase.  The endpoint
exception records a stationary phase change before the first genuine movement of the new pass. -/
private def previousDirectionCompatible {n : Nat}
    (cfg : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (previous : Option LBA.HeadTurns.Direction) : Prop :=
  if n = 0 then True else
    match cfg.state with
    | none => True
    | some .initFirst => previous = none
    | some .initSweep => RightCompatible cfg previous
    | some .initBack => LeftCompatible cfg previous
    | some .scanRight | some (.query _) | some (.putRight _) =>
        RightCompatible cfg previous
    | some .scanLeft | some (.putLeft _) =>
        LeftCompatible cfg previous

private lemma sweeping_rightMove {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : RightCompatible source previous) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .right⟩ ∧
      RightCompatible
        ⟨state, (source.tape.write written).moveHead .right⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .right⟩) := by
  by_cases hhead : source.tape.head.val < n
  · have hdirection := physicalDirection_write_moveHead_right_of_lt
      source state written hhead
    constructor
    · apply (LBA.Sweeping.turnAllowed_of_physicalDirection_eq_some
        previous source _ .right hdirection).2
      rcases hprevious with rfl | rfl | ⟨rfl, hzero⟩
      · simp
      · simp
      · exact Or.inr (Or.inl hzero)
    · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_some
        previous source _ .right hdirection]
      simp [RightCompatible]
  · have hdirection := physicalDirection_write_moveHead_right_of_not_lt
      source state written hhead
    constructor
    · exact LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
        previous source _ hdirection
    · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_none
        previous source _ hdirection]
      simpa [RightCompatible, DLBA.BoundedTape.moveHead, hhead] using hprevious

private lemma sweeping_leftMove {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : LeftCompatible source previous) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .left⟩ ∧
      LeftCompatible
        ⟨state, (source.tape.write written).moveHead .left⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .left⟩) := by
  by_cases hhead : 0 < source.tape.head.val
  · have hdirection := physicalDirection_write_moveHead_left_of_pos
      source state written hhead
    constructor
    · apply (LBA.Sweeping.turnAllowed_of_physicalDirection_eq_some
        previous source _ .left hdirection).2
      rcases hprevious with rfl | rfl | ⟨rfl, hright⟩
      · simp
      · simp
      · exact Or.inr (Or.inr hright)
    · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_some
        previous source _ .left hdirection]
      simp [LeftCompatible]
  · have hdirection := physicalDirection_write_moveHead_left_of_not_pos
      source state written hhead
    constructor
    · exact LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
        previous source _ hdirection
    · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_none
        previous source _ hdirection]
      simpa [LeftCompatible, DLBA.BoundedTape.moveHead, hhead] using hprevious

private lemma sweeping_stayRight {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : RightCompatible source previous) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .stay⟩ ∧
      RightCompatible
        ⟨state, (source.tape.write written).moveHead .stay⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .stay⟩) := by
  have hdirection := physicalDirection_write_moveHead_stay source state written
  constructor
  · exact LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
      previous source _ hdirection
  · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_none
      previous source _ hdirection]
    simpa [RightCompatible, DLBA.BoundedTape.moveHead] using hprevious

private lemma sweeping_stayLeft {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : LeftCompatible source previous) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .stay⟩ ∧
      LeftCompatible
        ⟨state, (source.tape.write written).moveHead .stay⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .stay⟩) := by
  have hdirection := physicalDirection_write_moveHead_stay source state written
  constructor
  · exact LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
      previous source _ hdirection
  · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_none
      previous source _ hdirection]
    simpa [LeftCompatible, DLBA.BoundedTape.moveHead] using hprevious

/-- A rightward phase may turn left directly at a sound right endpoint. -/
private lemma sweeping_turnLeft {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction) (hn : n ≠ 0)
    (hendpoint : source.tape.head.val = n) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .left⟩ ∧
      LeftCompatible
        ⟨state, (source.tape.write written).moveHead .left⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .left⟩) := by
  have hpositive : 0 < source.tape.head.val := by omega
  have hdirection := physicalDirection_write_moveHead_left_of_pos
    source state written hpositive
  constructor
  · apply LBA.Sweeping.turnAllowed_of_atEndpoint (Or.inr hendpoint)
  · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_some
      previous source _ .left hdirection]
    simp [LeftCompatible]

/-- A stationary left-to-right phase change at cell zero preserves enough information for the
following right move. -/
private lemma sweeping_stayLeftToRight {n : Nat}
    (source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (state : Option (Phase Q)) (written : Alphabet I Gamma Q)
    (previous : Option LBA.HeadTurns.Direction) (hn : n ≠ 0)
    (hprevious : LeftCompatible source previous)
    (hendpoint : source.tape.head.val = 0) :
    LBA.Sweeping.TurnAllowed previous source
        ⟨state, (source.tape.write written).moveHead .stay⟩ ∧
      RightCompatible
        ⟨state, (source.tape.write written).moveHead .stay⟩
        (LBA.Sweeping.advanceDirection previous source
          ⟨state, (source.tape.write written).moveHead .stay⟩) := by
  have hdirection := physicalDirection_write_moveHead_stay source state written
  constructor
  · exact LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
      previous source _ hdirection
  · rw [LBA.Sweeping.advanceDirection_of_physicalDirection_eq_none
      previous source _ hdirection]
    rcases hprevious with rfl | rfl | ⟨rfl, hright⟩
    · simp [RightCompatible]
    · simp [RightCompatible, DLBA.BoundedTape.moveHead, hendpoint]
    · exfalso
      omega

/-! ## One-step sweeping discipline -/

private lemma sweeping_running_actual (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (phase : Phase Q)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hfirst : phase ≠ .initFirst) (hsweep : phase ≠ .initSweep)
    (hflags : FlagsSound tape) (previous : Option LBA.HeadTurns.Direction)
    (hn : n ≠ 0)
    (hprevious : previousDirectionCompatible
      (⟨some phase, tape⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨phase, tape⟩ = some target) :
    LBA.Sweeping.TurnAllowed previous
        ⟨some phase, tape⟩ ⟨some target.state, target.tape⟩ ∧
      previousDirectionCompatible ⟨some target.state, target.tape⟩
        (LBA.Sweeping.advanceDirection previous
          ⟨some phase, tape⟩ ⟨some target.state, target.tape⟩) := by
  cases phase with
  | initFirst => exact (hfirst rfl).elim
  | initSweep => exact (hsweep rfl).elim
  | initBack =>
      have hprev : LeftCompatible
          (⟨some Phase.initBack, tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hleft : cell.left <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread,
                  hleft] at hstep
              · subst target
                have hmove := sweeping_leftMove
                  (⟨some Phase.initBack, tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .initBack) (workSymbol (I := I) cell) previous hprev
                simpa [previousDirectionCompatible, hn, hleft] using hmove
              · subst target
                have hzero := (hflags tape.head cell hread).1 hleft
                have hmove := sweeping_stayLeftToRight
                  (⟨some Phase.initBack, tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .scanRight) (workSymbol (I := I) cell) previous hn hprev hzero
                simpa [previousDirectionCompatible, hn, hleft] using hmove
  | scanRight =>
      have hprev : RightCompatible
          (⟨some Phase.scanRight, tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases htag : cell.tag with
              | head state =>
                  simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, htag]
                    at hstep
                  subst target
                  have hmove := sweeping_stayRight
                    (⟨some Phase.scanRight, tape⟩ :
                      DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                    (some (.query state)) (workSymbol (I := I) cell) previous hprev
                  simpa [previousDirectionCompatible, hn] using hmove
              | plain =>
                  cases hright : cell.right <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                      continueRight, hread, htag, hright] at hstep
                  · subst target
                    have hmove := sweeping_rightMove
                      (⟨some Phase.scanRight, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanRight) (workSymbol (I := I) cell) previous hprev
                    simpa [previousDirectionCompatible, hn, hright] using hmove
                  · subst target
                    have hend := (hflags tape.head cell hread).2 hright
                    have hmove := sweeping_turnLeft
                      (⟨some Phase.scanRight, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanLeft) (workSymbol (I := I) cell) previous hn hend
                    simpa [previousDirectionCompatible, hn, hright] using hmove
              | needLeft state =>
                  cases hright : cell.right <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                      continueRight, hread, htag, hright] at hstep
                  · subst target
                    have hmove := sweeping_rightMove
                      (⟨some Phase.scanRight, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanRight) (workSymbol (I := I) cell) previous hprev
                    simpa [previousDirectionCompatible, hn, hright] using hmove
                  · subst target
                    have hend := (hflags tape.head cell hread).2 hright
                    have hmove := sweeping_turnLeft
                      (⟨some Phase.scanRight, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanLeft) (workSymbol (I := I) cell) previous hn hend
                    simpa [previousDirectionCompatible, hn, hright] using hmove
  | query state =>
      have hprev : RightCompatible
          (⟨some (Phase.query state), tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hsource : M.transition state cell.symbol with
              | none =>
                  simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread,
                    hsource] at hstep
              | some move =>
                  rcases move with ⟨next, written, direction⟩
                  cases direction with
                  | stay =>
                      cases hright : cell.right <;>
                        simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                          continueRight, hread, hsource, hright] at hstep
                      · subst target
                        let newCell := cell.writeTagged written (.head next)
                        have hmove := sweeping_rightMove
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some .scanRight) (workSymbol (I := I) newCell) previous hprev
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hright] using hmove
                      · subst target
                        have hend := (hflags tape.head cell hread).2 hright
                        let newCell := cell.writeTagged written (.head next)
                        have hmove := sweeping_turnLeft
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some .scanLeft) (workSymbol (I := I) newCell) previous hn hend
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hright] using hmove
                  | right =>
                      cases hright : cell.right <;>
                        simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                          continueRight, hread, hsource, hright] at hstep
                      · subst target
                        let newCell := cell.writeTagged written .plain
                        have hmove := sweeping_rightMove
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some (.putRight next)) (workSymbol (I := I) newCell) previous hprev
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hright] using hmove
                      · subst target
                        have hend := (hflags tape.head cell hread).2 hright
                        let newCell := cell.writeTagged written (.head next)
                        have hmove := sweeping_turnLeft
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some .scanLeft) (workSymbol (I := I) newCell) previous hn hend
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hright] using hmove
                  | left =>
                      cases hleft : cell.left <;>
                        cases hright : cell.right <;>
                          simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                            continueRight, hread, hsource, hleft, hright] at hstep
                      · subst target
                        let newCell := cell.writeTagged written (.needLeft next)
                        have hmove := sweeping_rightMove
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some .scanRight) (workSymbol (I := I) newCell) previous hprev
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hleft, hright] using hmove
                      · subst target
                        have hend := (hflags tape.head cell hread).2 hright
                        let newCell := cell.writeTagged written .plain
                        have hmove := sweeping_turnLeft
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some (.putLeft next)) (workSymbol (I := I) newCell) previous hn hend
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hleft, hright] using hmove
                      · subst target
                        let newCell := cell.writeTagged written (.head next)
                        have hmove := sweeping_rightMove
                          (⟨some (Phase.query state), tape⟩ :
                            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                          (some .scanRight) (workSymbol (I := I) newCell) previous hprev
                        simpa [newCell, Cell.writeTagged, previousDirectionCompatible, hn,
                          hleft, hright] using hmove
                      · have hzero := (hflags tape.head cell hread).1 hleft
                        have hend := (hflags tape.head cell hread).2 hright
                        exfalso
                        omega
  | putRight state =>
      have hprev : RightCompatible
          (⟨some (Phase.putRight state), tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hright : cell.right <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                  continueRight, hread, hright] at hstep
              · subst target
                let newCell := cell.withTag (.head state)
                have hmove := sweeping_rightMove
                  (⟨some (Phase.putRight state), tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .scanRight) (workSymbol (I := I) newCell) previous hprev
                simpa [newCell, Cell.withTag, previousDirectionCompatible, hn, hright]
                  using hmove
              · subst target
                have hend := (hflags tape.head cell hread).2 hright
                let newCell := cell.withTag (.head state)
                have hmove := sweeping_turnLeft
                  (⟨some (Phase.putRight state), tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .scanLeft) (workSymbol (I := I) newCell) previous hn hend
                simpa [newCell, Cell.withTag, previousDirectionCompatible, hn, hright]
                  using hmove
  | scanLeft =>
      have hprev : LeftCompatible
          (⟨some Phase.scanLeft, tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases htag : cell.tag with
              | needLeft state =>
                  simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread, htag]
                    at hstep
                  subst target
                  let newCell := cell.withTag .plain
                  have hmove := sweeping_leftMove
                    (⟨some Phase.scanLeft, tape⟩ :
                      DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                    (some (.putLeft state)) (workSymbol (I := I) newCell) previous hprev
                  simpa [newCell, Cell.withTag, previousDirectionCompatible, hn] using hmove
              | plain =>
                  cases hleft : cell.left <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                      continueLeft, hread, htag, hleft] at hstep
                  · subst target
                    have hmove := sweeping_leftMove
                      (⟨some Phase.scanLeft, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanLeft) (workSymbol (I := I) cell) previous hprev
                    simpa [previousDirectionCompatible, hn, hleft] using hmove
                  · subst target
                    have hzero := (hflags tape.head cell hread).1 hleft
                    have hmove := sweeping_stayLeftToRight
                      (⟨some Phase.scanLeft, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanRight) (workSymbol (I := I) cell) previous hn hprev hzero
                    simpa [previousDirectionCompatible, hn, hleft] using hmove
              | head state =>
                  cases hleft : cell.left <;>
                    simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                      continueLeft, hread, htag, hleft] at hstep
                  · subst target
                    have hmove := sweeping_leftMove
                      (⟨some Phase.scanLeft, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanLeft) (workSymbol (I := I) cell) previous hprev
                    simpa [previousDirectionCompatible, hn, hleft] using hmove
                  · subst target
                    have hzero := (hflags tape.head cell hread).1 hleft
                    have hmove := sweeping_stayLeftToRight
                      (⟨some Phase.scanLeft, tape⟩ :
                        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                      (some .scanRight) (workSymbol (I := I) cell) previous hn hprev hzero
                    simpa [previousDirectionCompatible, hn, hleft] using hmove
  | putLeft state =>
      have hprev : LeftCompatible
          (⟨some (Phase.putLeft state), tape⟩ :
            DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
        simpa [previousDirectionCompatible, hn] using hprevious
      cases hread : tape.contents tape.head with
      | none => simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
      | some observed =>
          cases observed with
          | inl input =>
              simp [DLBA.step, DLBA.BoundedTape.read, machine, transition, hread] at hstep
          | inr cell =>
              cases hleft : cell.left <;>
                simp [DLBA.step, DLBA.BoundedTape.read, machine, transition,
                  continueLeft, hread, hleft] at hstep
              · subst target
                let newCell := cell.withTag (.head state)
                have hmove := sweeping_leftMove
                  (⟨some (Phase.putLeft state), tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .scanLeft) (workSymbol (I := I) newCell) previous hprev
                simpa [newCell, Cell.withTag, previousDirectionCompatible, hn, hleft]
                  using hmove
              · subst target
                have hzero := (hflags tape.head cell hread).1 hleft
                let newCell := cell.withTag (.head state)
                have hmove := sweeping_stayLeftToRight
                  (⟨some (Phase.putLeft state), tape⟩ :
                    DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
                  (some .scanRight) (workSymbol (I := I) newCell) previous hn hprev hzero
                simpa [newCell, Cell.withTag, previousDirectionCompatible, hn, hleft]
                  using hmove

private lemma sweeping_initFirst_actual (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I)
    (previous : Option LBA.HeadTurns.Direction) (hn : n ≠ 0)
    (hprevious : previousDirectionCompatible
      (⟨some Phase.initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed)
      ⟨.initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩ = some target) :
    LBA.Sweeping.TurnAllowed previous
        ⟨some Phase.initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩
        ⟨some target.state, target.tape⟩ ∧
      previousDirectionCompatible ⟨some target.state, target.tape⟩
        (LBA.Sweeping.advanceDirection previous
          ⟨some Phase.initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩
          ⟨some target.state, target.tape⟩) := by
  let source : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n :=
    ⟨some .initFirst, ⟨fun index => inputEmbed (input index), 0⟩⟩
  let cell : Cell Gamma Q := ⟨true, false, embed (input 0), .head M.initial⟩
  have htarget : target =
      ⟨.initSweep, (source.tape.write (workSymbol (I := I) cell)).moveHead .right⟩ := by
    simpa [source, cell, DLBA.step, DLBA.BoundedTape.read, machine, transition]
      using hstep.symm
  subst target
  have hnone : previous = none := by
    simpa [source, previousDirectionCompatible, hn] using hprevious
  have hright : RightCompatible source previous := Or.inl hnone
  have hmove := sweeping_rightMove source (some .initSweep)
    (workSymbol (I := I) cell) previous hright
  simpa [source, cell, previousDirectionCompatible, hn] using hmove

private lemma sweeping_initSweepRaw_actual (M : DLBA.Machine Gamma Q)
    (embed : I -> Gamma) {n : Nat} (input : Fin (n + 1) -> I)
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hsuffix : RawSuffix input tape) (previous : Option LBA.HeadTurns.Direction)
    (hn : n ≠ 0)
    (hprevious : previousDirectionCompatible
      (⟨some Phase.initSweep, tape⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨.initSweep, tape⟩ = some target) :
    LBA.Sweeping.TurnAllowed previous
        ⟨some Phase.initSweep, tape⟩ ⟨some target.state, target.tape⟩ ∧
      previousDirectionCompatible ⟨some target.state, target.tape⟩
        (LBA.Sweeping.advanceDirection previous
          ⟨some Phase.initSweep, tape⟩ ⟨some target.state, target.tape⟩) := by
  have hread := hsuffix tape.head (by omega)
  let cell : Cell Gamma Q := ⟨false, false, embed (input tape.head), .plain⟩
  have htarget : target =
      ⟨.initSweep, (tape.write (workSymbol (I := I) cell)).moveHead .right⟩ := by
    simpa [cell, DLBA.step, DLBA.BoundedTape.read, machine, transition, inputEmbed,
      hread] using hstep.symm
  subst target
  have hright : RightCompatible
      (⟨some Phase.initSweep, tape⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) previous := by
    simpa [previousDirectionCompatible, hn] using hprevious
  have hmove := sweeping_rightMove
    (⟨some Phase.initSweep, tape⟩ :
      DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (some .initSweep) (workSymbol (I := I) cell) previous hright
  simpa [cell, previousDirectionCompatible, hn] using hmove

private lemma sweeping_initSweepEnd_actual (M : DLBA.Machine Gamma Q)
    (embed : I -> Gamma) {n : Nat}
    (tape : DLBA.BoundedTape (Alphabet I Gamma Q) n)
    (hhead : tape.head.val = n) (cell : Cell Gamma Q)
    (hread : tape.contents tape.head = workSymbol (I := I) cell)
    (previous : Option LBA.HeadTurns.Direction) (hn : n ≠ 0)
    {target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hstep : DLBA.step (machine M embed) ⟨.initSweep, tape⟩ = some target) :
    LBA.Sweeping.TurnAllowed previous
        ⟨some Phase.initSweep, tape⟩ ⟨some target.state, target.tape⟩ ∧
      previousDirectionCompatible ⟨some target.state, target.tape⟩
        (LBA.Sweeping.advanceDirection previous
          ⟨some Phase.initSweep, tape⟩ ⟨some target.state, target.tape⟩) := by
  let newCell : Cell Gamma Q := { cell with right := true }
  have htarget : target =
      ⟨.initBack, (tape.write (workSymbol (I := I) newCell)).moveHead .left⟩ := by
    simpa [newCell, DLBA.step, DLBA.BoundedTape.read, machine, transition, hread]
      using hstep.symm
  subst target
  have hmove := sweeping_turnLeft
    (⟨some Phase.initSweep, tape⟩ :
      DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
    (some .initBack) (workSymbol (I := I) newCell) previous hn hhead
  simpa [newCell, previousDirectionCompatible, hn] using hmove

/-- Every concrete simulator step obeys the turn rule, updates phase compatibility, and
preserves the geometric soundness invariant. -/
private lemma sweepingStep_of_soundClaim [DecidableEq (Alphabet I Gamma Q)]
    (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I)
    {source target : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n}
    (hsource : SoundClaim M embed input source)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : previousDirectionCompatible source previous)
    (hstep : LBA.Step (DLBA.toLBA' (machine M embed)) source target) :
    LBA.Sweeping.TurnAllowed previous source target ∧
      previousDirectionCompatible target
        (LBA.Sweeping.advanceDirection previous source target) ∧
      SoundClaim M embed input target := by
  have hnext : SoundClaim M embed input target := hsource.next M embed input hstep
  by_cases hn : n = 0
  · subst n
    refine ⟨LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
      previous source target (LBA.Sweeping.physicalDirection_width_zero source target), ?_, hnext⟩
    simp [previousDirectionCompatible]
  · cases hsource with
    | initFirst =>
        rcases DLBA.toLBA'_step_cases (machine M embed) .initFirst _ target hstep with
          hactual | hhalt
        · obtain ⟨phase, tape, rfl, hmachine⟩ := hactual
          obtain ⟨hallowed, hcompatible⟩ :=
            sweeping_initFirst_actual M embed input previous hn hprevious hmachine
          exact ⟨hallowed, hcompatible, hnext⟩
        · rcases hhalt with ⟨rfl, _, haccept⟩
          simp at haccept
    | initSweepRaw tape hpositive hsuffix hflags =>
        rcases DLBA.toLBA'_step_cases (machine M embed) .initSweep tape target hstep with
          hactual | hhalt
        · obtain ⟨phase, targetTape, rfl, hmachine⟩ := hactual
          obtain ⟨hallowed, hcompatible⟩ :=
            sweeping_initSweepRaw_actual M embed input tape hsuffix previous hn
              hprevious hmachine
          exact ⟨hallowed, hcompatible, hnext⟩
        · rcases hhalt with ⟨rfl, _, haccept⟩
          simp at haccept
    | initSweepEnd tape hhead cell hread hflags =>
        rcases DLBA.toLBA'_step_cases (machine M embed) .initSweep tape target hstep with
          hactual | hhalt
        · obtain ⟨phase, targetTape, rfl, hmachine⟩ := hactual
          obtain ⟨hallowed, hcompatible⟩ :=
            sweeping_initSweepEnd_actual M embed tape hhead cell hread previous hn hmachine
          exact ⟨hallowed, hcompatible, hnext⟩
        · rcases hhalt with ⟨rfl, _, haccept⟩
          simp at haccept
    | running phase tape hfirst hsweep hflags =>
        rcases DLBA.toLBA'_step_cases (machine M embed) phase tape target hstep with
          hactual | hhalt
        · obtain ⟨next, targetTape, rfl, hmachine⟩ := hactual
          obtain ⟨hallowed, hcompatible⟩ :=
            sweeping_running_actual M embed phase tape hfirst hsweep hflags previous hn
              hprevious hmachine
          exact ⟨hallowed, hcompatible, hnext⟩
        · rcases hhalt with ⟨rfl, _, _⟩
          have hdirection : LBA.HeadTurns.physicalDirection
              (⟨some phase, tape⟩ :
                DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n)
              ⟨none, tape⟩ = none := by
            simp [LBA.HeadTurns.physicalDirection]
          refine ⟨LBA.Sweeping.turnAllowed_of_physicalDirection_eq_none
            previous _ _ hdirection, ?_, hnext⟩
          simp [previousDirectionCompatible, hn]
    | terminal tape hflags =>
        obtain ⟨next, written, direction, hmem, _⟩ := hstep
        simp [DLBA.toLBA'] at hmem

/-- The local phase invariant proves sweeping for every finite trace, not just accepting runs. -/
private theorem sweepingFrom_of_soundClaim [DecidableEq (Alphabet I Gamma Q)]
    (M : DLBA.Machine Gamma Q) (embed : I -> Gamma)
    {n : Nat} (input : Fin (n + 1) -> I)
    {source target : DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n}
    (trace : LBA.StepTrace (DLBA.toLBA' (machine M embed)) source target)
    (hsource : SoundClaim M embed input source)
    (previous : Option LBA.HeadTurns.Direction)
    (hprevious : previousDirectionCompatible source previous) :
    trace.SweepingFrom previous := by
  induction trace generalizing previous with
  | refl => trivial
  | @head source next target hstep rest ih =>
      obtain ⟨hallowed, hcompatible, hnext⟩ :=
        sweepingStep_of_soundClaim M embed input hsource previous hprevious hstep
      exact (LBA.StepTrace.sweepingFrom_head hstep rest previous).2
        ⟨hallowed, ih hnext _ hcompatible⟩

/-- The deterministic same-width simulator is sweeping on every canonically embedded nonempty
input.  The promise ranges over all concrete finite prefixes, including rejecting computations;
the one-cell case and the stationary accepting bridge of `DLBA.toLBA'` are included. -/
public theorem machine_sweepingViaEmbed [DecidableEq (Alphabet I Gamma Q)]
    (M : DLBA.Machine Gamma Q) (embed : I -> Gamma) :
    (machine M embed).SweepingViaEmbed (inputEmbed (Γ := Gamma) (Q := Q)) := by
  intro n input target trace
  have hsource : SoundClaim M embed input
      (⟨some Phase.initFirst,
        ⟨fun index => inputEmbed (Γ := Gamma) (Q := Q) (input index), 0⟩⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) :=
    SoundClaim.initFirst
  have hprevious : previousDirectionCompatible
      (⟨some Phase.initFirst,
        ⟨fun index => inputEmbed (Γ := Gamma) (Q := Q) (input index), 0⟩⟩ :
        DLBA.Cfg (Alphabet I Gamma Q) (Option (Phase Q)) n) none := by
    simp [previousDirectionCompatible]
  exact sweepingFrom_of_soundClaim M embed input trace hsource none hprevious

end DeterministicSweeping

end DLBA
