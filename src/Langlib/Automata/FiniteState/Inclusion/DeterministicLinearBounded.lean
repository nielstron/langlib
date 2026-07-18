module

public import Langlib.Automata.FiniteState.Equivalence.Determinization
public import Langlib.Automata.LinearBounded.BoundedCrossing
public import Langlib.Automata.LinearBounded.Equivalence.DeterministicEndmarkerToFlag
import Mathlib.Tactic

@[expose]
public section

/-!
# Finite-state languages are deterministic linearly bounded

A DFA can be run directly by a one-way scan of the canonical bracketed tape
`⊢ w ⊣`.  The construction below leaves every tape cell unchanged, stores only the
current DFA state in finite control, and enters a halting state when it reads `⊣`.
It is locally functional, so the general functional-endmarker folding theorem turns
it into a machine in the library's marker-free `is_DLBA` presentation.

The semantic construction is uniform in the input alphabet, DFA state type, and work
alphabet.  In particular, the empty word is not treated as an external exception: the
scanner runs from `⊢` directly to `⊣` on the canonical two-cell tape.

## Main results

* `DFA.endmarkerLBA` -- the explicit one-way endmarker LBA for a DFA.
* `DFA.endmarkerLBA_functional` -- its local transition relation is single-valued.
* `DFA.languageEnd_endmarkerLBA_eq` -- exact language equality, including `[]`.
* `DFA.endmarkerTrace` -- the concrete one-way scan as a Type-valued LBA trace.
* `DFA.crossingCount_endmarkerTrace` -- every physical boundary is crossed exactly once.
* `DFA.endmarkerLBA_hasUniformAcceptingBound_one` -- the scanner's explicit uniform crossing cap.
* `is_DLBA_of_is_DFA` and `is_DLBA_of_is_NFA` -- class-level inclusions.
* `DFA_subset_DLBA` and `NFA_subset_DLBA` -- set-theoretic forms.
-/

namespace DFA

open Classical

variable {T Q Work : Type*}

/-- Finite control of the endmarker scanner.  `scan q` means that `q` is the DFA
state after the already-scanned input prefix; `halt q` records the final DFA state. -/
public inductive EndmarkerLBAState (Q : Type*) where
  | scan : Q → EndmarkerLBAState Q
  | halt : Q → EndmarkerLBAState Q
deriving Fintype, DecidableEq

/-- Local transition relation for the canonical endmarker scan.  Ill-formed tape
symbols simply have no successor. -/
public noncomputable def endmarkerLBATransition (D : DFA T Q) :
    EndmarkerLBAState Q → LBA.EndAlpha T Work →
      Set (EndmarkerLBAState Q × LBA.EndAlpha T Work × DLBA.Dir)
  | .scan q, .inr false => {(.scan q, LBA.leftMark, .right)}
  | .scan q, .inl (some (.inl input)) =>
      {(.scan (D.step q input), .inl (some (.inl input)), .right)}
  | .scan q, .inr true => {(.halt q, LBA.rightMark, .stay)}
  | .scan _, .inl _ => ∅
  | .halt _, _ => ∅

/-- The one-way endmarker LBA that evaluates `D`. -/
public noncomputable def endmarkerLBA (D : DFA T Q) :
    LBA.Machine (LBA.EndAlpha T Work) (EndmarkerLBAState Q) where
  transition := endmarkerLBATransition D
  accept
    | .scan _ => false
    | .halt q => decide (q ∈ D.accept)
  initial := .scan D.start

/-- The DFA scanner has at most one enabled move at every state/symbol pair. -/
public theorem endmarkerLBA_functional (D : DFA T Q) :
    (endmarkerLBA (Work := Work) D).Functional := by
  intro state symbol left hleft right hright
  cases state with
  | scan q =>
      rcases symbol with (interior | marker)
      · rcases interior with (_ | tagged)
        · simp [endmarkerLBA, endmarkerLBATransition] at hleft
        · rcases tagged with (input | work)
          · simpa [endmarkerLBA, endmarkerLBATransition] using hleft.trans hright.symm
          · simp [endmarkerLBA, endmarkerLBATransition] at hleft
      · rcases marker with (_ | _)
        · simpa [endmarkerLBA, endmarkerLBATransition] using hleft.trans hright.symm
        · simpa [endmarkerLBA, endmarkerLBATransition] using hleft.trans hright.symm
  | halt q =>
      simp [endmarkerLBA, endmarkerLBATransition] at hleft

private lemma cfg_ext {A S : Type*} {n : ℕ} {left right : DLBA.Cfg A S n}
    (hstate : left.state = right.state)
    (hcontents : left.tape.contents = right.tape.contents)
    (hhead : left.tape.head = right.tape.head) :
    left = right := by
  rcases left with ⟨leftState, leftContents, leftHead⟩
  rcases right with ⟨rightState, rightContents, rightHead⟩
  simp_all

@[simp] private lemma loadEnd_zero (word : List T) :
    (LBA.loadEnd (Γ := Work) word).contents ⟨0, by omega⟩ = LBA.leftMark := by
  simp [LBA.loadEnd]

@[simp] private lemma loadEnd_input (word : List T) (index : ℕ)
    (hindex : index < word.length) :
    (LBA.loadEnd (Γ := Work) word).contents ⟨index + 1, by omega⟩ =
      Sum.inl (some (Sum.inl word[index])) := by
  simp [LBA.loadEnd, hindex]

@[simp] private lemma loadEnd_right (word : List T) :
    (LBA.loadEnd (Γ := Work) word).contents ⟨word.length + 1, by omega⟩ =
      LBA.rightMark := by
  simp [LBA.loadEnd]

/-- Canonical scanner configuration after exactly `index` input symbols have
been consumed.  Its head is on input cell `index`, or on `⊣` when
`index = word.length`. -/
public noncomputable def endmarkerScanCfg (D : DFA T Q) (word : List T)
    (index : ℕ) (hindex : index ≤ word.length) :
    DLBA.Cfg (LBA.EndAlpha T Work) (EndmarkerLBAState Q) (word.length + 1) :=
  ⟨.scan (D.evalFrom D.start (word.take index)),
    ⟨(LBA.loadEnd (Γ := Work) word).contents, ⟨index + 1, by omega⟩⟩⟩

/-- Canonical halted configuration after the complete input has been scanned. -/
public noncomputable def endmarkerHaltCfg (D : DFA T Q) (word : List T) :
    DLBA.Cfg (LBA.EndAlpha T Work) (EndmarkerLBAState Q) (word.length + 1) :=
  ⟨.halt (D.eval word),
    ⟨(LBA.loadEnd (Γ := Work) word).contents,
      ⟨word.length + 1, by omega⟩⟩⟩

public theorem endmarker_initial_scan_step (D : DFA T Q) (word : List T) :
    LBA.Step (endmarkerLBA (Work := Work) D)
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word)
      (endmarkerScanCfg (Work := Work) D word 0 (Nat.zero_le _)) := by
  refine ⟨.scan D.start, LBA.leftMark, .right, ?_, ?_⟩
  · change _ ∈ endmarkerLBATransition D (.scan D.start) LBA.leftMark
    rfl
  · apply cfg_ext
    · simp [endmarkerScanCfg]
    · simp only [endmarkerScanCfg, LBA.initCfgEnd, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Work) word).contents =
        Function.update (LBA.loadEnd (Γ := Work) word).contents ⟨0, by omega⟩
          LBA.leftMark
      rw [← loadEnd_zero (Work := Work) word, Function.update_eq_self]
    · apply Fin.ext
      simp [LBA.initCfgEnd, LBA.loadEnd, endmarkerScanCfg,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

public theorem endmarker_scan_step (D : DFA T Q) (word : List T) (index : ℕ)
    (hindex : index < word.length) :
    LBA.Step (endmarkerLBA (Work := Work) D)
      (endmarkerScanCfg (Work := Work) D word index hindex.le)
      (endmarkerScanCfg (Work := Work) D word (index + 1) hindex) := by
  let input := word[index]
  refine ⟨.scan (D.step (D.evalFrom D.start (word.take index)) input),
    Sum.inl (some (Sum.inl input)), .right, ?_, ?_⟩
  · have hread :
        (endmarkerScanCfg (Work := Work) D word index hindex.le).tape.read =
          Sum.inl (some (Sum.inl input)) := by
      simp [endmarkerScanCfg, DLBA.BoundedTape.read, input,
        loadEnd_input, hindex]
    rw [hread]
    change _ ∈ endmarkerLBATransition D
      (.scan (D.evalFrom D.start (word.take index)))
      (Sum.inl (some (Sum.inl input)))
    rfl
  · apply cfg_ext
    · simp only [endmarkerScanCfg, input]
      rw [← DFA.evalFrom_append_singleton, List.take_concat_get' word index hindex]
    · simp only [endmarkerScanCfg, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Work) word).contents =
        Function.update (LBA.loadEnd (Γ := Work) word).contents
          ⟨index + 1, by omega⟩ (Sum.inl (some (Sum.inl input)))
      rw [show Sum.inl (some (Sum.inl input)) =
          (LBA.loadEnd (Γ := Work) word).contents ⟨index + 1, by omega⟩ by
        symm
        exact loadEnd_input (Work := Work) word index hindex,
        Function.update_eq_self]
    · apply Fin.ext
      simp only [endmarkerScanCfg, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      rw [dif_pos (by omega)]

private lemma scan_reaches (D : DFA T Q) (word : List T)
    (index : ℕ) (hindex : index ≤ word.length) :
    LBA.Reaches (endmarkerLBA (Work := Work) D)
      (endmarkerScanCfg (Work := Work) D word 0 (Nat.zero_le _))
      (endmarkerScanCfg (Work := Work) D word index hindex) := by
  induction index with
  | zero => exact Relation.ReflTransGen.refl
  | succ index ih =>
      exact (ih (by omega)).tail (endmarker_scan_step D word index (by omega))

public theorem endmarker_scan_right_step (D : DFA T Q) (word : List T) :
    LBA.Step (endmarkerLBA (Work := Work) D)
      (endmarkerScanCfg (Work := Work) D word word.length le_rfl)
      (endmarkerHaltCfg (Work := Work) D word) := by
  refine ⟨.halt (D.eval word), LBA.rightMark, .stay, ?_, ?_⟩
  · have hread :
        (endmarkerScanCfg (Work := Work) D word word.length le_rfl).tape.read =
          LBA.rightMark := by
      simp [endmarkerScanCfg, DLBA.BoundedTape.read]
    rw [hread]
    change _ ∈ endmarkerLBATransition D
      (.scan (D.evalFrom D.start (word.take word.length))) LBA.rightMark
    rw [List.take_length]
    rfl
  · apply cfg_ext
    · simp [endmarkerHaltCfg, DFA.eval]
    · simp only [endmarkerScanCfg, endmarkerHaltCfg,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Work) word).contents =
        Function.update (LBA.loadEnd (Γ := Work) word).contents
          ⟨word.length + 1, by omega⟩ LBA.rightMark
      rw [← loadEnd_right (Work := Work) word, Function.update_eq_self]
    · apply Fin.ext
      rfl

private def EndmarkerInv (D : DFA T Q) (word : List T)
    (cfg : DLBA.Cfg (LBA.EndAlpha T Work) (EndmarkerLBAState Q)
      (word.length + 1)) : Prop :=
  LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word = cfg ∨
  (∃ (index : ℕ) (hindex : index ≤ word.length),
    endmarkerScanCfg (Work := Work) D word index hindex = cfg) ∨
  endmarkerHaltCfg (Work := Work) D word = cfg

private lemma endmarkerInv_step (D : DFA T Q) (word : List T)
    {cfg cfg' : DLBA.Cfg (LBA.EndAlpha T Work) (EndmarkerLBAState Q)
      (word.length + 1)}
    (hinv : EndmarkerInv (Work := Work) D word cfg)
    (hstep : LBA.Step (endmarkerLBA (Work := Work) D) cfg cfg') :
    EndmarkerInv (Work := Work) D word cfg' := by
  rcases hstep with ⟨state', written, direction, hmove, rfl⟩
  rcases hinv with hinitial | hscan | hhalt
  · rw [← hinitial] at hmove ⊢
    have hread :
        (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word).tape.read =
          LBA.leftMark := by
      change (LBA.loadEnd (Γ := Work) word).contents
        (LBA.loadEnd (Γ := Work) word).head = LBA.leftMark
      exact loadEnd_zero (Work := Work) word
    rw [hread] at hmove
    change (state', written, direction) ∈
      endmarkerLBATransition D (.scan D.start) LBA.leftMark at hmove
    simp only [endmarkerLBATransition, Set.mem_singleton_iff] at hmove
    rcases hmove with ⟨rfl, rfl, rfl⟩
    right; left
    refine ⟨0, Nat.zero_le _, ?_⟩
    apply cfg_ext
    · simp [endmarkerScanCfg]
    · simp only [endmarkerScanCfg, LBA.initCfgEnd, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Work) word).contents =
        Function.update (LBA.loadEnd (Γ := Work) word).contents ⟨0, by omega⟩
          LBA.leftMark
      rw [← loadEnd_zero (Work := Work) word, Function.update_eq_self]
    · apply Fin.ext
      simp [LBA.initCfgEnd, LBA.loadEnd, endmarkerScanCfg,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · rcases hscan with ⟨index, hindex, hcfg⟩
    rw [← hcfg] at hmove ⊢
    by_cases hlast : index = word.length
    · subst index
      have hread :
          (endmarkerScanCfg (Work := Work) D word word.length le_rfl).tape.read =
            LBA.rightMark := by
        simp [endmarkerScanCfg, DLBA.BoundedTape.read]
      rw [hread] at hmove
      change (state', written, direction) ∈
        endmarkerLBATransition D
          (.scan (D.evalFrom D.start (word.take word.length))) LBA.rightMark at hmove
      rw [List.take_length] at hmove
      simp only [endmarkerLBATransition, Set.mem_singleton_iff] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      right; right
      apply cfg_ext
      · simp [endmarkerHaltCfg, DFA.eval]
      · simp only [endmarkerScanCfg, endmarkerHaltCfg,
          DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        change (LBA.loadEnd (Γ := Work) word).contents =
          Function.update (LBA.loadEnd (Γ := Work) word).contents
            ⟨word.length + 1, by omega⟩ LBA.rightMark
        rw [← loadEnd_right (Work := Work) word, Function.update_eq_self]
      · apply Fin.ext
        rfl
    · have hindex' : index < word.length := lt_of_le_of_ne hindex hlast
      let input := word[index]
      have hread :
          (endmarkerScanCfg (Work := Work) D word index hindex).tape.read =
            Sum.inl (some (Sum.inl input)) := by
        simp [endmarkerScanCfg, DLBA.BoundedTape.read, input,
          loadEnd_input, hindex']
      rw [hread] at hmove
      change (state', written, direction) ∈
        endmarkerLBATransition D
          (.scan (D.evalFrom D.start (word.take index)))
          (Sum.inl (some (Sum.inl input))) at hmove
      simp only [endmarkerLBATransition, Set.mem_singleton_iff] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      right; left
      refine ⟨index + 1, hindex', ?_⟩
      apply cfg_ext
      · simp only [endmarkerScanCfg, input]
        rw [← DFA.evalFrom_append_singleton,
          List.take_concat_get' word index hindex']
      · simp only [endmarkerScanCfg, DLBA.BoundedTape.write,
          DLBA.BoundedTape.moveHead]
        change (LBA.loadEnd (Γ := Work) word).contents =
          Function.update (LBA.loadEnd (Γ := Work) word).contents
            ⟨index + 1, by omega⟩ (Sum.inl (some (Sum.inl input)))
        rw [show Sum.inl (some (Sum.inl input)) =
            (LBA.loadEnd (Γ := Work) word).contents ⟨index + 1, by omega⟩ by
          symm
          exact loadEnd_input (Work := Work) word index hindex',
          Function.update_eq_self]
      · apply Fin.ext
        simp only [endmarkerScanCfg, DLBA.BoundedTape.write,
          DLBA.BoundedTape.moveHead]
        rw [dif_pos (by omega)]
  · rw [← hhalt] at hmove
    change (state', written, direction) ∈
      endmarkerLBATransition D (.halt (D.eval word)) LBA.rightMark at hmove
    simp [endmarkerLBATransition] at hmove

private lemma endmarkerInv_reaches (D : DFA T Q) (word : List T)
    {cfg : DLBA.Cfg (LBA.EndAlpha T Work) (EndmarkerLBAState Q)
      (word.length + 1)}
    (hreach : LBA.Reaches (endmarkerLBA (Work := Work) D)
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word) cfg) :
    EndmarkerInv (Work := Work) D word cfg := by
  induction hreach with
  | refl => exact Or.inl rfl
  | tail _ hstep ih => exact endmarkerInv_step D word ih hstep

/-- Exact acceptance characterization of the explicit endmarker scanner. -/
public theorem endmarkerLBA_accepts_iff (D : DFA T Q) (word : List T) :
    LBA.Accepts (endmarkerLBA (Work := Work) D)
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word) ↔
      word ∈ D.accepts := by
  constructor
  · rintro ⟨cfg, hreach, haccept⟩
    rcases endmarkerInv_reaches (Work := Work) D word hreach with
      hinitial | hscan | hhalt
    · rw [← hinitial] at haccept
      simp [endmarkerLBA, LBA.initCfgEnd] at haccept
    · rcases hscan with ⟨index, hindex, hcfg⟩
      rw [← hcfg] at haccept
      simp [endmarkerLBA, endmarkerScanCfg] at haccept
    · rw [← hhalt] at haccept
      have hfinal : D.eval word ∈ D.accept := by
        simpa [endmarkerLBA, endmarkerHaltCfg] using haccept
      exact (DFA.mem_accepts D).mpr hfinal
  · intro haccept
    refine ⟨endmarkerHaltCfg (Work := Work) D word, ?_, ?_⟩
    · exact (Relation.ReflTransGen.single (endmarker_initial_scan_step D word)).trans
        ((scan_reaches D word word.length le_rfl).trans
          (Relation.ReflTransGen.single (endmarker_scan_right_step D word)))
    · have hfinal : D.eval word ∈ D.accept := (DFA.mem_accepts D).mp haccept
      simpa [endmarkerLBA, endmarkerHaltCfg] using hfinal

/-- The explicit one-way endmarker LBA recognizes exactly the DFA language. -/
public theorem languageEnd_endmarkerLBA_eq (D : DFA T Q) :
    LBA.LanguageEnd (endmarkerLBA (Work := Work) D) = D.accepts := by
  ext word
  exact endmarkerLBA_accepts_iff (Work := Work) D word

/-! ### Exact crossing behavior of the one-way scanner -/

/-- The concrete right-moving scanner trace after `index` input symbols.  It starts with the
head on the first input cell (or on the right marker for the empty word) and moves once for each
consumed input symbol. -/
public noncomputable def endmarkerScanTrace (D : DFA T Q) (word : List T) :
    (index : Nat) → (hindex : index ≤ word.length) →
      LBA.StepTrace (endmarkerLBA (Work := Work) D)
        (endmarkerScanCfg (Work := Work) D word 0 (Nat.zero_le _))
        (endmarkerScanCfg (Work := Work) D word index hindex)
  | 0, _ => .refl _
  | index + 1, hindex =>
      LBA.StepTrace.append
        (endmarkerScanTrace D word index (by omega))
        (LBA.StepTrace.single (endmarker_scan_step D word index (by omega)))

/-- The full concrete scanner trace, including departure from the left marker and the final
stationary transition on the right marker. -/
public noncomputable def endmarkerTrace (D : DFA T Q) (word : List T) :
    LBA.StepTrace (endmarkerLBA (Work := Work) D)
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word)
      (endmarkerHaltCfg (Work := Work) D word) :=
  LBA.StepTrace.append
    (LBA.StepTrace.single (endmarker_initial_scan_step D word))
    (LBA.StepTrace.append
      (endmarkerScanTrace D word word.length le_rfl)
      (LBA.StepTrace.single (endmarker_scan_right_step D word)))

private theorem crosses_initial_scan_iff (D : DFA T Q) (word : List T)
    (boundary : Fin (word.length + 1)) :
    LBA.StepTrace.CrossesBoundary boundary
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word)
      (endmarkerScanCfg (Work := Work) D word 0 (Nat.zero_le _)) ↔
        boundary.val = 0 := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight, LBA.initCfgEnd, LBA.loadEnd,
    endmarkerScanCfg]
  omega

private theorem crosses_scan_step_iff (D : DFA T Q) (word : List T)
    (index : Nat) (hindex : index < word.length)
    (boundary : Fin (word.length + 1)) :
    LBA.StepTrace.CrossesBoundary boundary
      (endmarkerScanCfg (Work := Work) D word index hindex.le)
      (endmarkerScanCfg (Work := Work) D word (index + 1) hindex) ↔
        boundary.val = index + 1 := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight, endmarkerScanCfg]
  omega

private theorem not_crosses_scan_halt (D : DFA T Q) (word : List T)
    (boundary : Fin (word.length + 1)) :
    ¬ LBA.StepTrace.CrossesBoundary boundary
      (endmarkerScanCfg (Work := Work) D word word.length le_rfl)
      (endmarkerHaltCfg (Work := Work) D word) := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight, endmarkerScanCfg, endmarkerHaltCfg]
  omega

/-- During the input-cell portion of the scan, boundary `b` has been crossed exactly when it is
strictly positive and no farther right than the current scan index. -/
public theorem crossingCount_endmarkerScanTrace (D : DFA T Q) (word : List T)
    (index : Nat) (hindex : index ≤ word.length)
    (boundary : Fin (word.length + 1)) :
    (endmarkerScanTrace (Work := Work) D word index hindex).crossingCount boundary =
      if 0 < boundary.val ∧ boundary.val ≤ index then 1 else 0 := by
  induction index with
  | zero =>
      rw [show endmarkerScanTrace (Work := Work) D word 0 hindex = .refl _ from rfl,
        LBA.StepTrace.crossingCount_refl,
        if_neg (by omega : ¬ (0 < boundary.val ∧ boundary.val ≤ 0))]
  | succ index ih =>
      have hlt : index < word.length := by omega
      rw [endmarkerScanTrace, LBA.StepTrace.crossingCount_append,
        ih (by omega), LBA.StepTrace.crossingCount_single]
      simp only [crosses_scan_step_iff (Work := Work) D word index hlt boundary]
      by_cases hprevious : 0 < boundary.val ∧ boundary.val ≤ index
      · rw [if_pos hprevious, if_neg (by omega : boundary.val ≠ index + 1),
          if_pos (by omega : 0 < boundary.val ∧ boundary.val ≤ index + 1)]
      · rw [if_neg hprevious]
        by_cases hcurrent : boundary.val = index + 1
        · rw [if_pos hcurrent,
            if_pos (by omega : 0 < boundary.val ∧ boundary.val ≤ index + 1)]
        · rw [if_neg hcurrent,
            if_neg (by omega : ¬ (0 < boundary.val ∧ boundary.val ≤ index + 1))]

/-- Every physical tape boundary is crossed exactly once by the full DFA scanner trace. -/
public theorem crossingCount_endmarkerTrace (D : DFA T Q) (word : List T)
    (boundary : Fin (word.length + 1)) :
    (endmarkerTrace (Work := Work) D word).crossingCount boundary = 1 := by
  rw [endmarkerTrace, LBA.StepTrace.crossingCount_append,
    LBA.StepTrace.crossingCount_single,
    LBA.StepTrace.crossingCount_append,
    crossingCount_endmarkerScanTrace,
    LBA.StepTrace.crossingCount_single]
  rw [if_neg (not_crosses_scan_halt (Work := Work) D word boundary)]
  by_cases hzero : boundary.val = 0
  · rw [if_pos ((crosses_initial_scan_iff (Work := Work) D word boundary).2 hzero)]
    simp [hzero]
  · have hpositive : 0 < boundary.val := Nat.pos_of_ne_zero hzero
    have hle : boundary.val ≤ word.length := by omega
    rw [if_neg (fun hcross => hzero
      ((crosses_initial_scan_iff (Work := Work) D word boundary).1 hcross)),
      if_pos ⟨hpositive, hle⟩]

/-- The one-way endmarker LBA for a DFA has a uniform selected-accepting crossing cap of `1`:
every accepted word has the explicit scanner trace above, and that trace crosses every boundary
exactly once.  (For a language with no accepted words, the semantic promise is also vacuously
true at cap zero.) -/
public theorem endmarkerLBA_hasUniformAcceptingBound_one (D : DFA T Q) :
    LBA.BoundedCrossing.HasUniformAcceptingBound
      (endmarkerLBA (Work := Work) D) 1 := by
  intro word haccept
  have hdfa : word ∈ D.accepts :=
    (endmarkerLBA_accepts_iff (Work := Work) D word).mp haccept
  refine ⟨endmarkerHaltCfg (Work := Work) D word,
    endmarkerTrace (Work := Work) D word, ?_, ?_⟩
  · have hfinal : D.eval word ∈ D.accept := (DFA.mem_accepts D).mp hdfa
    simpa [endmarkerLBA, endmarkerHaltCfg] using hfinal
  · intro boundary
    rw [crossingCount_endmarkerTrace]

end DFA

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Every language with a finite-state deterministic presentation has a deterministic
linearly bounded presentation. -/
public theorem is_DLBA_of_is_DFA {L : Language T} (hL : is_DFA L) : is_DLBA L := by
  classical
  obtain ⟨Q, hQ, D, hD⟩ := hL
  letI : Fintype Q := hQ
  rw [← hD, ← DFA.languageEnd_endmarkerLBA_eq (Work := Unit) D]
  exact is_DLBA_languageEnd_of_functional
    (DFA.endmarkerLBA (Work := Unit) D)
    (DFA.endmarkerLBA_functional D)

/-- Every language with a finite-state nondeterministic presentation has a deterministic
linearly bounded presentation. -/
public theorem is_DLBA_of_is_NFA {L : Language T} (hL : is_NFA L) : is_DLBA L :=
  is_DLBA_of_is_DFA (is_NFA_iff_is_DFA.mp hL)

/-- Set-theoretic form of `is_DLBA_of_is_DFA`. -/
public theorem DFA_subset_DLBA :
    (DFA.Class : Set (Language T)) ⊆ DLBA := by
  intro L hL
  exact is_DLBA_of_is_DFA hL

/-- Set-theoretic form of `is_DLBA_of_is_NFA`. -/
public theorem NFA_subset_DLBA :
    (NFA.Class : Set (Language T)) ⊆ DLBA := by
  intro L hL
  exact is_DLBA_of_is_NFA hL

end
