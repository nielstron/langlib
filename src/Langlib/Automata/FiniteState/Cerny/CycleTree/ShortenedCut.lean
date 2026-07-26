module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.DepthPrefix
import Mathlib.Tactic.Linarith

@[expose]
public section

/-!
# The one-depth shortened cut word

The prefix `E = A^ell p²` removes the unique depth-`cycle` point of the
`D`-path.  Consequently `E D^(cycle - 1)` resets, extending the arithmetic
region covered by the raw word `D^cycle`.
-/

namespace DFA.CycleTree

/-- The one-depth prefix `E = A^ell p²`. -/
def shortenedCutPrefix (P : Params) : List Letter :=
  wordPow aWord P.ell ++ pSquared

@[simp]
theorem length_shortenedCutPrefix (P : Params) :
    (shortenedCutPrefix P).length = 4 * P.X + 6 := by
  simp [shortenedCutPrefix, Params.ell]
  omega

/-- `E` maps every state to the sink or to an interval coordinate other
than the unique deepest one. -/
theorem shortenedCutPrefix_avoidsDeep (P : Params) :
    PrefixAvoidsDeep P (shortenedCutPrefix P) 1 := by
  intro state
  obtain ⟨index, himage⟩ :=
    exists_aPower_ell_cycleState P state
  rw [shortenedCutPrefix, (automaton P).evalFrom_of_append,
    himage, evalFrom_pSquared_cycleState]
  by_cases hcut : index = rhoIndex P
  · left
    rw [if_pos hcut]
  · right
    refine ⟨index, ?_, ?_⟩
    · intro hdeep
      rcases hdeep with ⟨offset, hoffset, hindex⟩
      have hoffsetZero : offset = 0 := by omega
      subst offset
      simp only [Function.iterate_zero_apply] at hindex
      exact hcut hindex
    · rw [if_neg hcut]

/-- Arithmetic region covered by `E D^(cycle - 1)`, expressed without
truncated subtraction. -/
def ShortenedCutSafe (P : Params) : Prop :=
  P.R ^ 2 + P.R + 1 ≤
    P.X ^ 2 + P.X + P.L ^ 2 + P.L

/-- Exact cost check for the shortened cut word. -/
theorem shortenedCut_total_length_le_bound (P : Params)
    (hsafe : ShortenedCutSafe P) :
    (shortenedCutPrefix P).length +
        (P.cycle - 1) * (4 * P.m + 2) ≤
      (P.order - 1) ^ 2 := by
  rw [length_shortenedCutPrefix]
  simp only [ShortenedCutSafe] at hsafe
  simp only [Params.cycle, Params.m, Params.order, Params.ell]
  have hcycle :
      2 * P.R + 2 * P.L + 3 - 1 =
        2 * P.R + 2 * P.L + 2 := by
    omega
  have horder :
      2 * P.X + 2 + (2 * P.R + 2 * P.L + 3) - 1 =
        2 * (P.X + P.R + P.L) + 4 := by
    omega
  rw [hcycle, horder]
  nlinarith

/-- The shortened explicit word proves the Černý conclusion in its whole
cost-safe region. -/
theorem satisfiesCerny_of_coprime_of_shortenedCutSafe (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hsafe : ShortenedCutSafe P) :
    (automaton P).SatisfiesCerny := by
  apply satisfiesCerny_of_prefix_avoidsDeep P hcoprime
    (shortenedCutPrefix P) 1
  · omega
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt P.cycle_pos)
  · exact shortenedCutPrefix_avoidsDeep P
  · exact shortenedCut_total_length_le_bound P hsafe

/-- Synchronization supplies the coprimality premise automatically. -/
theorem satisfiesCerny_of_synchronizing_of_shortenedCutSafe (P : Params)
    (hsynchronizing : (automaton P).Synchronizing)
    (hsafe : ShortenedCutSafe P) :
    (automaton P).SatisfiesCerny :=
  satisfiesCerny_of_coprime_of_shortenedCutSafe P
    (coprime_of_synchronizing P hsynchronizing) hsafe

end DFA.CycleTree
