module

public import Langlib.Automata.LinearBounded.TwoMatchingChoiceBound
import Mathlib.Tactic

@[expose]
public section

/-!
# Transport of LBAs along tape-alphabet equivalences

Renaming the tape alphabet by an equivalence changes no raw computation.  This module records
the induced equivalences on bounded tapes and configurations, and transports the machine step
relation, reachability, acceptance, and exact two-matching presentations.

No finiteness or inhabitance assumption is needed for the semantic transport itself.
-/

namespace LBA

variable {Γ Γ' Λ : Type*}

/-- Rename every cell of a bounded tape along an alphabet equivalence. -/
@[expose]
public def alphabetEquivTape (equiv : Γ ≃ Γ') {n : ℕ} :
    DLBA.BoundedTape Γ n ≃ DLBA.BoundedTape Γ' n where
  toFun tape := ⟨equiv ∘ tape.contents, tape.head⟩
  invFun tape := ⟨equiv.symm ∘ tape.contents, tape.head⟩
  left_inv tape := by
    cases tape with
    | mk contents head =>
      change (⟨equiv.symm ∘ (equiv ∘ contents), head⟩ :
        DLBA.BoundedTape Γ n) = ⟨contents, head⟩
      congr 1
      funext index
      exact equiv.symm_apply_apply (contents index)
  right_inv tape := by
    cases tape with
    | mk contents head =>
      change (⟨equiv ∘ (equiv.symm ∘ contents), head⟩ :
        DLBA.BoundedTape Γ' n) = ⟨contents, head⟩
      congr 1
      funext index
      exact equiv.apply_symm_apply (contents index)

@[simp]
public theorem alphabetEquivTape_contents (equiv : Γ ≃ Γ') {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) :
    (alphabetEquivTape equiv tape).contents = equiv ∘ tape.contents := rfl

@[simp]
public theorem alphabetEquivTape_head (equiv : Γ ≃ Γ') {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) :
    (alphabetEquivTape equiv tape).head = tape.head := rfl

@[simp]
public theorem alphabetEquivTape_read (equiv : Γ ≃ Γ') {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) :
    (alphabetEquivTape equiv tape).read = equiv tape.read := rfl

@[simp]
public theorem alphabetEquivTape_write (equiv : Γ ≃ Γ') {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) (symbol : Γ) :
    alphabetEquivTape equiv (tape.write symbol) =
      (alphabetEquivTape equiv tape).write (equiv symbol) := by
  cases tape with
  | mk contents head =>
    change (⟨equiv ∘ Function.update contents head symbol, head⟩ :
      DLBA.BoundedTape Γ' n) =
      ⟨Function.update (equiv ∘ contents) head (equiv symbol), head⟩
    congr 1
    funext index
    by_cases hindex : index = head
    · subst index
      simp
    · simp [Function.update, hindex]

@[simp]
public theorem alphabetEquivTape_moveHead (equiv : Γ ≃ Γ') {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) (direction : DLBA.Dir) :
    alphabetEquivTape equiv (tape.moveHead direction) =
      (alphabetEquivTape equiv tape).moveHead direction := by
  cases direction <;> rfl

/-- Rename the tape component of a configuration, leaving the state unchanged. -/
@[expose]
public def alphabetEquivCfg (equiv : Γ ≃ Γ') {n : ℕ} :
    DLBA.Cfg Γ Λ n ≃ DLBA.Cfg Γ' Λ n where
  toFun cfg := ⟨cfg.state, alphabetEquivTape equiv cfg.tape⟩
  invFun cfg := ⟨cfg.state, alphabetEquivTape equiv.symm cfg.tape⟩
  left_inv cfg := by
    cases cfg with
    | mk state tape =>
      change (⟨state, alphabetEquivTape equiv.symm (alphabetEquivTape equiv tape)⟩ :
        DLBA.Cfg Γ Λ n) = ⟨state, tape⟩
      congr 1
      cases tape with
      | mk contents head =>
        change (⟨equiv.symm ∘ (equiv ∘ contents), head⟩ :
          DLBA.BoundedTape Γ n) = ⟨contents, head⟩
        congr 1
        funext index
        exact equiv.symm_apply_apply (contents index)
  right_inv cfg := by
    cases cfg with
    | mk state tape =>
      change (⟨state, alphabetEquivTape equiv (alphabetEquivTape equiv.symm tape)⟩ :
        DLBA.Cfg Γ' Λ n) = ⟨state, tape⟩
      congr 1
      cases tape with
      | mk contents head =>
        change (⟨equiv ∘ (equiv.symm ∘ contents), head⟩ :
          DLBA.BoundedTape Γ' n) = ⟨contents, head⟩
        congr 1
        funext index
        exact equiv.apply_symm_apply (contents index)

@[simp]
public theorem alphabetEquivCfg_state (equiv : Γ ≃ Γ') {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    (alphabetEquivCfg equiv cfg).state = cfg.state := rfl

@[simp]
public theorem alphabetEquivCfg_tape (equiv : Γ ≃ Γ') {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    (alphabetEquivCfg equiv cfg).tape = alphabetEquivTape equiv cfg.tape := rfl

@[simp]
public theorem alphabetEquivCfg_updateMove (equiv : Γ ≃ Γ') {n : ℕ}
    (state : Λ) (tape : DLBA.BoundedTape Γ n) (written : Γ)
    (direction : DLBA.Dir) :
    alphabetEquivCfg equiv
        (⟨state, (tape.write written).moveHead direction⟩ : DLBA.Cfg Γ Λ n) =
      ⟨state, ((alphabetEquivTape equiv tape).write (equiv written)).moveHead direction⟩ := by
  change (⟨state, alphabetEquivTape equiv ((tape.write written).moveHead direction)⟩ :
    DLBA.Cfg Γ' Λ n) = _
  rw [alphabetEquivTape_moveHead, alphabetEquivTape_write]

/-- Rename the read and written tape symbols of a machine along an equivalence. -/
@[expose]
public def Machine.alphabetTransport (M : Machine Γ Λ) (equiv : Γ ≃ Γ') :
    Machine Γ' Λ where
  transition state observed :=
    (fun output : Λ × Γ × DLBA.Dir => (output.1, equiv output.2.1, output.2.2)) ''
      M.transition state (equiv.symm observed)
  accept := M.accept
  initial := M.initial

@[simp]
public theorem Machine.mem_alphabetTransport_transition_iff
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ')
    (state target : Λ) (observed written : Γ') (direction : DLBA.Dir) :
    (target, written, direction) ∈ (M.alphabetTransport equiv).transition state observed ↔
      (target, equiv.symm written, direction) ∈ M.transition state (equiv.symm observed) := by
  constructor
  · rintro ⟨⟨outputTarget, outputWritten, outputDirection⟩, houtput, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, hwritten, rfl⟩
    have : outputWritten = equiv.symm written := by
      exact equiv.injective (hwritten.trans (equiv.apply_symm_apply written).symm)
    simpa [this] using houtput
  · intro houtput
    refine ⟨(target, equiv.symm written, direction), houtput, ?_⟩
    simp

@[simp]
public theorem Machine.alphabetTransport_accept
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') (state : Λ) :
    (M.alphabetTransport equiv).accept state = M.accept state := rfl

@[simp]
public theorem Machine.alphabetTransport_initial
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') :
    (M.alphabetTransport equiv).initial = M.initial := rfl

/-- A renamed machine has exactly the renamed one-step relation. -/
public theorem Machine.step_alphabetTransport_iff
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') {n : ℕ}
    (source target : DLBA.Cfg Γ Λ n) :
    Step (M.alphabetTransport equiv)
        (alphabetEquivCfg equiv source) (alphabetEquivCfg equiv target) ↔
      Step M source target := by
  constructor
  · rintro ⟨targetState, written, direction, htransition, htarget⟩
    have horiginal :
        (targetState, equiv.symm written, direction) ∈
          M.transition source.state source.tape.read := by
      simpa using htransition
    refine ⟨targetState, equiv.symm written, direction, horiginal, ?_⟩
    apply (alphabetEquivCfg equiv).injective
    rw [htarget]
    simp
  · rintro ⟨targetState, written, direction, htransition, rfl⟩
    refine ⟨targetState, equiv written, direction, ?_, ?_⟩
    · simpa using htransition
    · exact alphabetEquivCfg_updateMove equiv targetState source.tape written direction

/-- Equivalent arbitrary-target form of `step_alphabetTransport_iff`. -/
public theorem Machine.step_alphabetTransport_iff_symm
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') {n : ℕ}
    (source target : DLBA.Cfg Γ' Λ n) :
    Step (M.alphabetTransport equiv) source target ↔
      Step M ((alphabetEquivCfg equiv).symm source)
        ((alphabetEquivCfg equiv).symm target) := by
  simpa using M.step_alphabetTransport_iff equiv
    ((alphabetEquivCfg equiv).symm source) ((alphabetEquivCfg equiv).symm target)

/-- Reachability is invariant under an alphabet equivalence. -/
public theorem Machine.reaches_alphabetTransport_iff
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') {n : ℕ}
    (source target : DLBA.Cfg Γ Λ n) :
    Reaches (M.alphabetTransport equiv)
        (alphabetEquivCfg equiv source) (alphabetEquivCfg equiv target) ↔
      Reaches M source target := by
  have forward : ∀ {left right : DLBA.Cfg Γ Λ n}, Reaches M left right →
      Reaches (M.alphabetTransport equiv)
        (alphabetEquivCfg equiv left) (alphabetEquivCfg equiv right) := by
    intro left right hreach
    induction hreach with
    | refl => exact .refl
    | tail middle hstep ih =>
        exact ih.tail ((M.step_alphabetTransport_iff equiv _ _).2 hstep)
  have backward : ∀ {left right : DLBA.Cfg Γ' Λ n},
      Reaches (M.alphabetTransport equiv) left right →
      Reaches M ((alphabetEquivCfg equiv).symm left)
        ((alphabetEquivCfg equiv).symm right) := by
    intro left right hreach
    induction hreach with
    | refl => exact .refl
    | tail middle hstep ih =>
        exact ih.tail ((M.step_alphabetTransport_iff_symm equiv _ _).1 hstep)
  constructor
  · intro hreach
    simpa using backward hreach
  · intro hreach
    exact forward hreach

/-- Acceptance from corresponding configurations is invariant under alphabet renaming. -/
public theorem Machine.accepts_alphabetTransport_iff
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') {n : ℕ}
    (source : DLBA.Cfg Γ Λ n) :
    Accepts (M.alphabetTransport equiv) (alphabetEquivCfg equiv source) ↔
      Accepts M source := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    refine ⟨(alphabetEquivCfg equiv).symm target, ?_, ?_⟩
    · have := (M.reaches_alphabetTransport_iff equiv source
          ((alphabetEquivCfg equiv).symm target)).1 (by simpa using hreach)
      exact this
    · simpa using haccept
  · rintro ⟨target, hreach, haccept⟩
    exact ⟨alphabetEquivCfg equiv target,
      (M.reaches_alphabetTransport_iff equiv source target).2 hreach, haccept⟩

/-- Exact two-matching presentations are invariant under a tape-alphabet equivalence. -/
public theorem Machine.hasTwoMatchingStepPartition_alphabetTransport_iff
    (M : Machine Γ Λ) (equiv : Γ ≃ Γ') :
    (M.alphabetTransport equiv).HasTwoMatchingStepPartition ↔
      M.HasTwoMatchingStepPartition := by
  constructor
  · rintro ⟨layer, cover, subedge, biUnique, short⟩
    let sourceLayer : (n : ℕ) → Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop :=
      fun n color source target =>
        layer n color (alphabetEquivCfg equiv source) (alphabetEquivCfg equiv target)
    refine ⟨sourceLayer, ?_, ?_, ?_, ?_⟩
    · intro n source target
      rw [← M.step_alphabetTransport_iff equiv source target]
      exact cover n _ _
    · intro n color source target hlayer
      exact (M.step_alphabetTransport_iff equiv source target).1
        (subedge n color _ _ hlayer)
    · intro n color
      constructor
      · intro left right target hleft hright
        exact (alphabetEquivCfg equiv).injective
          ((biUnique n color).1 hleft hright)
      · intro source left right hleft hright
        exact (alphabetEquivCfg equiv).injective
          ((biUnique n color).2 hleft hright)
    · intro n color left middle right hleft hright
      exact short n color hleft hright
  · rintro ⟨layer, cover, subedge, biUnique, short⟩
    let targetLayer : (n : ℕ) → Fin 2 →
        DLBA.Cfg Γ' Λ n → DLBA.Cfg Γ' Λ n → Prop :=
      fun n color source target =>
        layer n color ((alphabetEquivCfg equiv).symm source)
          ((alphabetEquivCfg equiv).symm target)
    refine ⟨targetLayer, ?_, ?_, ?_, ?_⟩
    · intro n source target
      rw [M.step_alphabetTransport_iff_symm equiv source target]
      exact cover n _ _
    · intro n color source target hlayer
      exact (M.step_alphabetTransport_iff_symm equiv source target).2
        (subedge n color _ _ hlayer)
    · intro n color
      constructor
      · intro left right target hleft hright
        apply (alphabetEquivCfg equiv).symm.injective
        exact (biUnique n color).1 hleft hright
      · intro source left right hleft hright
        apply (alphabetEquivCfg equiv).symm.injective
        exact (biUnique n color).2 hleft hright
    · intro n color left middle right hleft hright
      exact short n color hleft hright

end LBA

end
