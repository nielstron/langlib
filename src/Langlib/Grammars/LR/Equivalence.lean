module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Grammars.LR.Equivalence.DPDAToLR
public import Langlib.Grammars.LR.Equivalence.LRkToDPDA

/-!
# LR(k) grammars and deterministic pushdown automata

For every fixed positive amount of lookahead, LR(k) grammars generate exactly
the languages accepted by deterministic pushdown automata.  The same is true
of the existential finite-lookahead LR class.
-/

@[expose]
public section

open Language

variable {T : Type} [Fintype T]

/-- For every positive `k`, LR(k) languages are exactly DPDA languages. -/
public theorem is_LRk_iff_is_DPDA {k : ℕ} (hk : 0 < k)
    {L : Language T} : is_LRk k L ↔ is_DPDA L := by
  constructor
  · exact is_DPDA_of_is_LRk
  · intro h
    exact is_LRk_mono (show 1 ≤ k by omega)
      (is_LRk_one_of_is_DPDA h)

/-- The existential finite-lookahead LR class is exactly the DPDA class. -/
public theorem is_LR_iff_is_DPDA {L : Language T} :
    is_LR L ↔ is_DPDA L :=
  ⟨is_DPDA_of_is_LR, is_LR_of_is_DPDA⟩

/-- Equality of the fixed positive-lookahead LR(k) and DPDA language classes. -/
public theorem LRk_eq_DPDA (k : ℕ) (hk : 0 < k) :
    LRk (T := T) k = DPDA.Class := by
  ext L
  exact is_LRk_iff_is_DPDA hk

/-- Equality of the existential finite-lookahead LR and DPDA classes. -/
public theorem LR_eq_DPDA : LR (T := T) = DPDA.Class := by
  ext L
  exact is_LR_iff_is_DPDA

/-- DCF is the conventional class name for the same fixed positive-lookahead
equivalence. -/
public theorem is_LRk_iff_is_DCF {k : ℕ} (hk : 0 < k)
    {L : Language T} : is_LRk k L ↔ is_DCF L := by
  simpa [is_DCF] using (is_LRk_iff_is_DPDA (T := T) hk (L := L))

/-- Existential finite-lookahead LR languages are exactly deterministic
context-free languages. -/
public theorem is_LR_iff_is_DCF {L : Language T} :
    is_LR L ↔ is_DCF L := by
  simpa [is_DCF] using (is_LR_iff_is_DPDA (T := T) (L := L))

/-- Class equality between fixed positive-lookahead LR(k) and DCF. -/
public theorem LRk_eq_DCF (k : ℕ) (hk : 0 < k) :
    LRk (T := T) k = DCF := by
  simpa [DCF] using (LRk_eq_DPDA (T := T) k hk)

/-- Class equality between existential finite-lookahead LR and DCF. -/
public theorem LR_eq_DCF : LR (T := T) = DCF := by
  simpa [DCF] using (LR_eq_DPDA (T := T))

end
