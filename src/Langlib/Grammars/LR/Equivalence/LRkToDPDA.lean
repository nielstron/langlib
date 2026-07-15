module

public import Langlib.Grammars.LR.Equivalence.MachineCorrectness
public import Langlib.Grammars.LR.Equivalence.Endmarker

/-!
# LR(k) grammars compile to deterministic pushdown automata

The concrete parser reads an explicit fresh endmarker.  Correctness on marked
words is proved at the automaton level, and the endmarker is then removed by
deterministic-context-free closure under regular quotient and inverse
injective renaming.
-/

@[expose]
public section

open Language

namespace CF_grammar.LRk

variable {T : Type} [Fintype T]

noncomputable section

/-- A positive-lookahead LR grammar is recognized by the concrete marked
parser after the fresh endmarker is removed. -/
private theorem is_DPDA_CF_language_of_IsLRk_pos (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k) (hLR : G.IsLRk k) :
    is_DPDA (CF_language G) := by
  let M := Buffered.machine G k hk
  have hmachine : is_DCF M.acceptsByFinalState := by
    change is_DPDA M.acceptsByFinalState
    exact ⟨Buffered.Control G k, Buffered.StackSymbol G k,
      inferInstance, inferInstance, M, rfl⟩
  have hmarked : is_DCF (endmarked (CF_language G)) :=
    is_DCF_endmarked_of_marked_machine (CF_language G)
      M.acceptsByFinalState hmachine
      (Buffered.marked_machine_correct G k hk hLR)
  exact is_DCF_of_is_DCF_endmarked (CF_language G) hmarked

/-- Every LR(k) grammar language is deterministic context-free.  The
construction uses `k+1` lookahead slots so it also covers `k = 0`. -/
public theorem is_DPDA_CF_language_of_IsLRk (G : CF_grammar T) (k : ℕ)
    (hLR : G.IsLRk k) : is_DPDA (CF_language G) := by
  have hLR' : G.IsLRk (k + 1) :=
    CF_grammar.IsLRk.mono G (by omega) hLR
  exact is_DPDA_CF_language_of_IsLRk_pos G (k + 1) (by omega) hLR'

end

end CF_grammar.LRk

/-- Exact language-class inclusion: every LR(k) language is accepted by a
DPDA, for every finite `k` (including zero lookahead). -/
public theorem is_DPDA_of_is_LRk {T : Type} [Fintype T]
    {k : ℕ} {L : Language T} (h : is_LRk k L) : is_DPDA L := by
  rcases h with ⟨G, hLR, hL⟩
  rw [← hL]
  exact CF_grammar.LRk.is_DPDA_CF_language_of_IsLRk G k hLR

/-- Consequently, every LR language (LR(k) for some finite `k`) is accepted
by a DPDA. -/
public theorem is_DPDA_of_is_LR {T : Type} [Fintype T]
    {L : Language T} (h : is_LR L) : is_DPDA L := by
  rcases h with ⟨k, hk⟩
  exact is_DPDA_of_is_LRk hk

end
