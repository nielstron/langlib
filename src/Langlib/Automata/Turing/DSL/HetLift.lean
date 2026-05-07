import Mathlib
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.BlockRealizability

/-! # Lifting Block Machines to Heterogeneous Tapes

This file contains the generic alphabet embedding used to run a block machine
over `Γ₀` on the `Sum.inr` portion of a heterogeneous tape
`Option (T ⊕ Γ₀)`.
-/

open Turing

/-! ### Lifting block-realizability to heterogeneous tape -/

/-- Embedding from Γ₀ to Option (T ⊕ Γ₀): default ↦ none, g ↦ some (inr g). -/
noncomputable def hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : Option (T ⊕ Γ₀) :=
  if g = default then none else some (Sum.inr g)

/-- Inverse of hetEmb: none ↦ default, some (inr g) ↦ g, some (inl _) ↦ default. -/
def hetInv {Γ₀ : Type} [Inhabited Γ₀] (T : Type) : Option (T ⊕ Γ₀) → Γ₀
  | none => default
  | some (Sum.inr g) => g
  | some (Sum.inl _) => default

theorem hetInv_hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : hetInv T (hetEmb T g) = g := by
  simp [hetEmb, hetInv]; split_ifs <;> simp_all

theorem hetEmb_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) : hetEmb T (default : Γ₀) = (none : Option (T ⊕ Γ₀)) := by
  simp [hetEmb]

theorem hetEmb_ne_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) (hg : g ≠ default) :
    hetEmb T g = some (Sum.inr g) := by
  simp [hetEmb, hg]

theorem map_hetEmb_block {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (block : List Γ₀) (hblock : ∀ g ∈ block, g ≠ default) :
    block.map (hetEmb T) = block.map (some ∘ @Sum.inr T Γ₀) := by
  simp only [List.map_inj_left]
  intro g hg
  exact hetEmb_ne_default T g (hblock g hg)

theorem tm0Het_liftBlockToHet
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T]
    (f : List Γ₀ → List Γ₀)
    (hf : TM0RealizesBlock Γ₀ f) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ (block : List Γ₀),
        (∀ g ∈ block, g ≠ default) →
        (∀ g ∈ f block, g ≠ default) →
        (TM0Seq.evalCfg M (block.map (some ∘ @Sum.inr T Γ₀))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (block.map (some ∘ @Sum.inr T Γ₀))).Dom),
          ((TM0Seq.evalCfg M
            (block.map (some ∘ @Sum.inr T Γ₀))).get h).Tape =
            Tape.mk₁ ((f block).map (some ∘ @Sum.inr T Γ₀)) := by
  obtain ⟨Λ, _, _, M, hM⟩ := hf
  refine' ⟨Λ, _, _, TM0AlphabetSim.liftMachine M (hetEmb T) (hetInv T), _⟩
  · infer_instance
  · intro block hblock hfblock
    obtain ⟨h_dom, h_tape⟩ := hM block [] hblock (by simp) hfblock
    have h_lift : ∃ b₂, TM0AlphabetSim.liftRel (hetEmb T) (hetInv T)
        (hetInv_hetEmb T) (hetEmb_default T)
        ((TM0Seq.evalCfg M (block ++ [default])).get h_dom) b₂ ∧
        b₂ ∈ TM0Seq.evalCfg
          (TM0AlphabetSim.liftMachine M (hetEmb T) (hetInv T))
          (List.map (some ∘ Sum.inr) block) := by
      convert Turing.tr_eval _ _ _
      exact TM0.step M
      exact TM0AlphabetSim.lift_respects M (hetEmb T) (hetInv T)
        (hetInv_hetEmb T) (hetEmb_default T)
      exact TM0.init (block ++ [default])
      · simp +decide [TM0AlphabetSim.liftRel, TM0.init]
        rw [tape_mk₁_append_default]
        unfold TM0AlphabetSim.embPM
        simp +decide [Tape.map_mk₁]
        rw [map_hetEmb_block]
        assumption
      · exact Part.get_mem h_dom
    obtain ⟨b₂, hb₂₁, hb₂₂⟩ := h_lift
    have h_tape_b₂ :
        b₂.Tape =
          Tape.mk₁ ((f block ++ [default]).map
            (TM0AlphabetSim.embPM (hetEmb T) (hetEmb_default T))) := by
      obtain ⟨_, h₂⟩ := hb₂₁
      rw [h₂, h_tape h_dom]
      exact Tape.map_mk₁ (TM0AlphabetSim.embPM (hetEmb T) (hetEmb_default T))
        (f block ++ [default])
    have h_tape_b₂_simplified :
        b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr) ++ [none]) := by
      convert h_tape_b₂ using 2
      simp +decide [TM0AlphabetSim.embPM, hetEmb]
      exact hfblock
    have h_tape_b₂_final :
        b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr)) := by
      convert tape_mk₁_append_default (List.map (some ∘ Sum.inr) (f block)) using 1
    cases hb₂₂
    aesop
