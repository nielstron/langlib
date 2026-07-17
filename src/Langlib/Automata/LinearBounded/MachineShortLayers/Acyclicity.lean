module

public import Langlib.Automata.LinearBounded.MachineShortLayers.Layering
public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
public import Langlib.Automata.LinearBounded.FiniteAcyclicRank

@[expose]
public section

/-!
# Acyclicity of the local four-phase compiler

A strict source rank lifts to the phase potential

* `core u`: `4 * rank u + 3`;
* `chosen u`: `4 * rank u + 4`;
* `landed v`: `4 * rank v + 1`;
* `pad v`: `4 * rank v + 2`.

The only edge crossing source ranks is `chosen → landed`.  A genuine source step raises the
major rank, so its target potential is at least `4 * rank u + 5`.  The other three edges raise
the phase component by one.  The proof applies to all raw configurations.
-/

namespace LBA.MachineShortLayers

open Classical Relation

variable {Γ Λ : Type*}

/-- Lift a strict source-configuration rank through the four protocol phases. -/
@[expose]
public def Potential [Fintype Γ] [Fintype Λ] {n : ℕ}
    (rank : DLBA.Cfg Γ Λ n → ℕ) :
    DLBA.Cfg Γ (ShortLayerState Γ Λ) n → ℕ
  | ⟨.core state, tape⟩ => 4 * rank ⟨state, tape⟩ + 3
  | ⟨.chosen source _ _, tape⟩ => 4 * rank ⟨source, tape⟩ + 4
  | ⟨.landed target, tape⟩ => 4 * rank ⟨target, tape⟩ + 1
  | ⟨.pad target, tape⟩ => 4 * rank ⟨target, tape⟩ + 2

/-- Every compiled step strictly raises the lifted phase potential whenever genuine source
steps strictly raise the supplied source rank. -/
public theorem potential_lt_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (rank : DLBA.Cfg Γ Λ n → ℕ)
    (hstrict : ∀ ⦃source target⦄,
      Step M source target → rank source < rank target)
    {old new : DLBA.Cfg Γ (ShortLayerState Γ Λ) n}
    (hstep : Step M.shortLayers old new) :
    Potential rank old < Potential rank new := by
  rcases old with ⟨state, tape⟩
  cases state with
  | core source =>
      obtain ⟨move, henabled, rfl⟩ :=
        (M.step_shortLayers_core_iff source tape new).mp hstep
      simp only [Potential]
      omega
  | chosen source expected move =>
      obtain ⟨hread, henabled, rfl⟩ :=
        (M.step_shortLayers_chosen_iff source expected move tape new).mp hstep
      have horiginal : Step M
          (⟨source, tape⟩ : DLBA.Cfg Γ Λ n)
          ⟨move.1, (tape.write move.2.1).moveHead move.2.2⟩ := by
        refine ⟨move.1, move.2.1, move.2.2, ?_, rfl⟩
        rw [hread]
        exact henabled
      have hrank := hstrict horiginal
      simp only [Potential]
      omega
  | landed target =>
      have hnew := (M.step_shortLayers_landed_iff target tape new).mp hstep
      subst new
      simp only [Potential]
      omega
  | pad target =>
      have hnew := (M.step_shortLayers_pad_iff target tape new).mp hstep
      subst new
      simp only [Potential]
      omega

/-- The local four-phase compiler preserves global configuration acyclicity at every width. -/
public theorem _root_.LBA.Machine.shortLayers_configurationAcyclic
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.shortLayers.ConfigurationAcyclic := by
  intro n cfg
  obtain ⟨rank, hstrict⟩ :=
    FiniteAcyclicRank.exists_strictRank (hacyclic n)
  exact FiniteAcyclicRank.acyclic_of_strictRank
    (edge := Step M.shortLayers) (rank := Potential rank)
    (fun {_ _} hstep => potential_lt_of_step M rank hstrict hstep) cfg

/-- Consequently, applying the four-phase compiler after the simultaneous degree serializer
preserves acyclicity of an acyclic source machine. -/
public theorem _root_.LBA.Machine.boundedDegree_shortLayers_configurationAcyclic
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.boundedDegree.shortLayers.ConfigurationAcyclic :=
  M.boundedDegree.shortLayers_configurationAcyclic
    (LBA.AcyclicBoundedDegree.configurationAcyclic_boundedDegree M hacyclic)

end LBA.MachineShortLayers

end
