module

public import Langlib.Automata.DeterministicPushdown.Normalization.FirstFinal
public import Langlib.Automata.Pushdown.Basics.FinalStateEmptyStack
public import Langlib.Automata.Pushdown.Equivalence.ContextFree.PDAToCFG
public import Langlib.Grammars.ContextFree.MathlibCFG
public import Langlib.Classes.ContextFree.Closure.PrefixBonus
public import Langlib.Grammars.LR.Definition

/-!
# The characteristic grammar of a deterministic pushdown automaton

This file fixes the construction used in the DPDA-to-LR(1) direction.

First, `DPDA.firstFinal` marks an epsilon phase after it has left a final
state.  The standard final-state-to-empty-stack conversion is then applied,
followed by the standard PDA characteristic grammar.  Finally, rules which
are not fully productive are removed.  Removing those rules is essential for
the LR argument: the target states guessed by the characteristic grammar must
actually be realizable by a computation.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The normalized PDA accepting by empty stack. -/
@[expose]
public noncomputable def emptyStackPDA (M : DPDA Q T S) :
    PDA ((Q × Bool) ⊕ Fin 2) T (Option S) :=
  PDA_FS_to_ES_pda M.firstFinal.toPDA

/-- Mathlib's characteristic grammar for the normalized empty-stack PDA. -/
@[expose]
public noncomputable def mathlibCharacteristicGrammar (M : DPDA Q T S) :
    ContextFreeGrammar T :=
  PDA_to_CFG.G (emptyStackPDA M)

/-- The same characteristic grammar in Langlib's `CF_grammar` representation. -/
@[expose]
public noncomputable def rawCharacteristicGrammar (M : DPDA Q T S) :
    CF_grammar T :=
  cfg_of_mathlib_cfg (mathlibCharacteristicGrammar M)

/-- The reduced characteristic grammar used for the LR(1) proof. -/
@[expose]
public noncomputable def characteristicGrammar (M : DPDA Q T S) :
    CF_grammar T :=
  productiveGrammar (rawCharacteristicGrammar M)

@[simp]
public theorem characteristicGrammar_nt (M : DPDA Q T S) :
    (characteristicGrammar M).nt =
      PDA_to_CFG.N (emptyStackPDA M) := rfl

@[simp]
public theorem characteristicGrammar_initial (M : DPDA Q T S) :
    (characteristicGrammar M).initial =
      PDA_to_CFG.N.start := rfl

/-- The complete language-equality chain for the characteristic grammar. -/
public theorem characteristicGrammar_language (M : DPDA Q T S) :
    CF_language (characteristicGrammar M) = M.acceptsByFinalState := by
  calc
    CF_language (characteristicGrammar M) =
        CF_language (rawCharacteristicGrammar M) :=
      productiveGrammar_language (rawCharacteristicGrammar M)
    _ = (mathlibCharacteristicGrammar M).language :=
      (mathlib_language_eq_CF_language (mathlibCharacteristicGrammar M)).symm
    _ = (emptyStackPDA M).acceptsByEmptyStack :=
      PDA_to_CFG.cfg_of_pda (emptyStackPDA M)
    _ = M.firstFinal.toPDA.acceptsByFinalState := by
      ext w
      exact ⟨PDA_FS_to_ES_backward M.firstFinal.toPDA w,
        PDA_FS_to_ES_forward M.firstFinal.toPDA w⟩
    _ = M.firstFinal.acceptsByFinalState := rfl
    _ = M.acceptsByFinalState := M.firstFinal_acceptsByFinalState

end

end DPDA_to_LR
