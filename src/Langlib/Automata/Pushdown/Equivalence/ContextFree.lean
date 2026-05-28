module

public import Langlib.Automata.Pushdown.Equivalence.ContextFree.CFGToPDA
public import Langlib.Automata.Pushdown.Equivalence.ContextFree.PDAToCFG
public import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Basics.FiniteNT
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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

/-- The class of context-free languages equals the class of PDA-recognizable languages. -/
theorem CF_eq_PDA_Class : (CF : Set (Language T)) = PDA.Class := by
  ext L
  exact is_CF_iff_isContextFree.trans is_PDA_iff_isContextFree.symm
