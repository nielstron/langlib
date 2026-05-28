import Langlib.Automata.DeterministicPushdown.Inclusion.Pushdown
import Langlib.Automata.Pushdown.Equivalence.ContextFree
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree

/-! # DPDAs are a strict subclass of PDAs

This file transfers the class-level strictness theorem `DCF ⊊ CF` to the
corresponding automaton classes.
-/

/-- DPDA final-state languages are a strict subclass of PDA languages over a
three-symbol alphabet. -/
theorem DPDA_strict_subclass_PDA :
    (DPDA.Class : Set (Language (Fin 3))) ⊂ PDA.Class := by
  rw [← CF_eq_PDA_Class]
  change (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3)))
  exact DCF_strict_subclass_CF
