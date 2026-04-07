import Langlib.Classes.ContextFree.Basics.Inclusion
import Langlib.Classes.ContextFree.Basics.FiniteNT
import Langlib.Automata.Pushdown.Equivalence.ContextFree.CFGToPDA
import Langlib.Automata.Pushdown.Equivalence.ContextFree.PDAToCFG

open PDA

variable {T : Type} [Fintype T]

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

/-- Every context-free language (with possibly infinite NT) is accepted by some PDA.
    This removes the `[Fintype g.NT]` requirement from `is_PDA_of_mathlib_cfg`
    by first restricting the grammar to one with finite nonterminals. -/
theorem is_PDA_of_isContextFree {L : Language T} (hL : L.IsContextFree) : is_PDA L := by
  obtain ⟨g, hfin, hg⟩ := ContextFreeGrammar.exists_fintype_nt L hL
  rw [← hg]
  haveI := hfin
  exact is_PDA_of_mathlib_cfg g

/-- The PDA-recognizable languages are exactly the context-free languages. -/
theorem is_PDA_iff_isContextFree {L : Language T} :
    is_PDA L ↔ L.IsContextFree :=
  ⟨isContextFree_of_is_PDA, is_PDA_of_isContextFree⟩
