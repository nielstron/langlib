import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.Pushdown.Equivalence.CFGToPDA
import Grammars.Classes.Pushdown.Equivalence.PDAToCFG

open PDA

variable {T : Type} [Fintype T]

/-- A language over a finite terminal alphabet is accepted by some PDA via empty-stack acceptance. -/
def is_PDA (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S), ∃ M : PDA Q T S, M.acceptsByEmptyStack = L

theorem is_PDA_of_mathlib_cfg (g : ContextFreeGrammar T) [Fintype g.NT] :
    is_PDA g.language := by
  classical
  refine ⟨CFG_to_PDA.Q, Symbol T g.NT, inferInstance, inferInstance, CFG_to_PDA.M g, ?_⟩
  symm
  exact CFG_to_PDA.pda_of_cfg g

theorem mathlib_cfg_of_PDA {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    (PDA_to_CFG.G M).language = M.acceptsByEmptyStack :=
  PDA_to_CFG.cfg_of_pda M

theorem isContextFree_of_is_PDA {L : Language T} :
    is_PDA L → L.IsContextFree := by
  rintro ⟨Q, S, _, _, M, hM⟩
  refine ⟨PDA_to_CFG.G M, ?_⟩
  simpa [hM] using PDA_to_CFG.cfg_of_pda M

theorem is_CF_of_is_PDA {L : Language T} :
    is_PDA L → is_CF L := by
  intro h
  rw [is_CF_iff_isContextFree]
  exact isContextFree_of_is_PDA h
