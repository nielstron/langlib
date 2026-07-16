module

public import Langlib.Classes.DeterministicContextFree.Inclusion.StrictContextFree
public import Langlib.Grammars.LR.Equivalence

/-!
# LR languages are a strict subclass of context-free languages

Positive-lookahead LR(k), existential-lookahead LR, and deterministic
context-free languages are the same language class.  Transporting the known
strict inclusion `DCF ⊊ CF` therefore gives the result directly for the LR
classes named in the hierarchy table.
-/

@[expose]
public section

open Language

/-- For every fixed positive `k`, LR(k) languages form a strict subclass of
context-free languages over a three-symbol alphabet. -/
public theorem LRk_strict_subclass_CF (k : ℕ) (hk : 0 < k) :
    (LRk (T := Fin 3) k : Set (Language (Fin 3))) ⊂
      (CF : Set (Language (Fin 3))) := by
  rw [LRk_eq_DCF k hk]
  exact DCF_strict_subclass_CF

/-- For every fixed positive `k`, LR(k) languages form a strict subclass of
context-free languages over any finite alphabet with at least three symbols. -/
public theorem LRk_strict_subclass_CF_of_card
    {T : Type} [Fintype T] (k : ℕ) (hk : 0 < k)
    (hT : 3 ≤ Fintype.card T) :
    (LRk (T := T) k : Set (Language T)) ⊂
      (CF : Set (Language T)) := by
  rw [LRk_eq_DCF k hk]
  exact DCF_strict_subclass_CF_of_card hT

/-- Existential finite-lookahead LR languages form a strict subclass of
context-free languages over a three-symbol alphabet. -/
public theorem LR_strict_subclass_CF :
    (LR : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) := by
  rw [LR_eq_DCF]
  exact DCF_strict_subclass_CF

/-- Existential finite-lookahead LR languages form a strict subclass of
context-free languages over any finite alphabet with at least three symbols. -/
public theorem LR_strict_subclass_CF_of_card
    {T : Type} [Fintype T] (hT : 3 ≤ Fintype.card T) :
    (LR : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  rw [LR_eq_DCF]
  exact DCF_strict_subclass_CF_of_card hT

end
