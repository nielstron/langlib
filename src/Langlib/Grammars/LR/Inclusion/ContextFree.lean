module

public import Langlib.Grammars.LR.Definition
public import Langlib.Classes.ContextFree.Definition

/-!
# LR(k) languages are context-free

Every LR(k) grammar is, by definition, a context-free grammar, so the language it
generates is context-free.  This file records that inclusion at the language-class
level.

## Main results

- `is_CF_of_is_LRk` — every LR(k) language is context-free
- `is_CF_of_is_LR` — every LR language is context-free
- `LR_subclass_CF` — `LR ⊆ CF`
-/

open Language

variable {T : Type}

/-- Every LR(k) language is context-free. -/
public theorem is_CF_of_is_LRk {k : ℕ} {L : Language T} (h : is_LRk k L) : is_CF L := by
  rcases h with ⟨g, _hg, hL⟩
  rw [is_CF_iff_isContextFree]
  exact ⟨g, hL⟩

/-- Every LR language is context-free. -/
public theorem is_CF_of_is_LR {L : Language T} (h : is_LR L) : is_CF L := by
  rcases h with ⟨k, hk⟩
  exact is_CF_of_is_LRk hk

/-- The class of LR languages is contained in the class of context-free languages. -/
public theorem LR_subclass_CF :
    (LR : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_LR hL
