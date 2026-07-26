module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.SyncCriterion

@[expose]
public section

/-!
# Prefix deletion and cut depth

The long residual words all have the same proof shape.  A prefix deletes
the first few deepest points of the cut-rotation path, after which a
shortened power of `D` resets.  This file proves that argument once,
independently of the concrete prefix.
-/

namespace DFA.CycleTree

/-- The first `depth` points on the backwards end of the `D`-path.

Offset zero is `rhoIndex`, the unique point requiring a full `cycle`
applications of `D`; subsequent offsets have successively smaller depth.
-/
def IsDeepIndex (P : Params) (depth : ℕ)
    (index : Fin P.cycle) : Prop :=
  ∃ offset < depth,
    index = (dIndex P)^[offset] (rhoIndex P)

/-- The underlying `D`-rotation has period `cycle`, independently of the
coprimality condition. -/
theorem iterate_dIndex_cycle (P : Params) (index : Fin P.cycle) :
    (dIndex P)^[P.cycle] index = index := by
  rw [iterate_dIndex]
  apply Fin.ext
  simp [cycleAdvance, Nat.mod_eq_of_lt index.isLt]

/-- A hit occurring too late would identify the starting point as one of
the explicitly deleted deep indices. -/
theorem dIndex_hit_le_of_not_deep (P : Params)
    (depth count : ℕ) (index : Fin P.cycle)
    (hdepth : depth ≤ P.cycle)
    (hhit : (dIndex P)^[count] index = rhoIndex P)
    (hcount : count < P.cycle)
    (hnotDeep : ¬IsDeepIndex P depth index) :
    count ≤ P.cycle - depth := by
  by_contra hnotLe
  have hcountLe : count ≤ P.cycle := Nat.le_of_lt hcount
  let offset := P.cycle - count
  have hoffsetLt : offset < depth := by
    dsimp [offset]
    omega
  apply hnotDeep
  refine ⟨offset, hoffsetLt, ?_⟩
  calc
    index = (dIndex P)^[P.cycle] index :=
      (iterate_dIndex_cycle P index).symm
    _ = (dIndex P)^[offset + count] index := by
      congr 2
      dsimp [offset]
      omega
    _ = (dIndex P)^[offset] ((dIndex P)^[count] index) :=
      Function.iterate_add_apply (dIndex P) offset count index
    _ = (dIndex P)^[offset] (rhoIndex P) := by rw [hhit]

/-- After deleting `depth` deep points, `cycle - depth` copies of `D`
reset every surviving interval coordinate. -/
theorem evalFrom_dPower_interval_of_not_deep (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (depth : ℕ) (hdepthPos : 0 < depth)
    (hdepth : depth ≤ P.cycle)
    (index : Fin P.cycle)
    (hnotDeep : ¬IsDeepIndex P depth index) :
    (automaton P).evalFrom (intervalState P index)
        (dPowerWord P (P.cycle - depth)) =
      P.stateOfNat 1 := by
  obtain ⟨count, hcountLt, hhitAdvance⟩ :=
    exists_dIndex_iterate_eq_rho P hcoprime index
  have hhit : (dIndex P)^[count] index = rhoIndex P := by
    rw [iterate_dIndex]
    exact hhitAdvance
  have hcountPos : 0 < count := by
    by_contra hnotPos
    have hzero : count = 0 := by omega
    subst count
    simp only [Function.iterate_zero_apply] at hhit
    apply hnotDeep
    refine ⟨0, hdepthPos, ?_⟩
    simpa only [Function.iterate_zero_apply] using hhit
  have hcountBound : count ≤ P.cycle - depth :=
    dIndex_hit_le_of_not_deep P depth count index hdepth hhit
      hcountLt hnotDeep
  have hreset :=
    evalFrom_dWordPower_interval_of_hit P index count hcountPos hhit
  unfold dPowerWord
  calc
    (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) (P.cycle - depth)) =
      (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) count ++
          wordPow (dWord P) (P.cycle - depth - count)) := by
            rw [← wordPow_add, Nat.add_sub_of_le hcountBound]
    _ = P.stateOfNat 1 := by
      rw [(automaton P).evalFrom_of_append, hreset,
        evalFrom_dWordPower_one]

/-- A pointwise formulation of the image condition needed from a prefix:
every image is the sink or an interval state outside the deleted depths. -/
def PrefixAvoidsDeep (P : Params) (preword : List Letter)
    (depth : ℕ) : Prop :=
  ∀ state,
    (automaton P).evalFrom state preword = P.stateOfNat 1 ∨
      ∃ index : Fin P.cycle,
        ¬IsDeepIndex P depth index ∧
          (automaton P).evalFrom state preword =
            intervalState P index

/-- Abstract prefix-deletion theorem underlying the residual `U` and `V`
constructions and the finite five-depth certificates. -/
theorem prefix_dPower_isResetWord (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (preword : List Letter) (depth : ℕ)
    (hdepthPos : 0 < depth) (hdepth : depth ≤ P.cycle)
    (hprefix : PrefixAvoidsDeep P preword depth) :
    (automaton P).IsResetWord
      (preword ++ dPowerWord P (P.cycle - depth)) := by
  refine ⟨P.stateOfNat 1, ?_⟩
  intro state
  rw [(automaton P).evalFrom_of_append]
  rcases hprefix state with hsink | ⟨index, hnotDeep, hindex⟩
  · rw [hsink]
    exact evalFrom_dWordPower_one P (P.cycle - depth)
  · rw [hindex]
    exact evalFrom_dPower_interval_of_not_deep P hcoprime depth
      hdepthPos hdepth index hnotDeep

/-- Prefix deletion plus the explicit word-length inequality proves the
Černý conclusion. -/
theorem satisfiesCerny_of_prefix_avoidsDeep (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (preword : List Letter) (depth : ℕ)
    (hdepthPos : 0 < depth) (hdepth : depth ≤ P.cycle)
    (hprefix : PrefixAvoidsDeep P preword depth)
    (hlength :
      preword.length + (P.cycle - depth) * (4 * P.m + 2) ≤
        (P.order - 1) ^ 2) :
    (automaton P).SatisfiesCerny := by
  apply DFA.satisfiesCerny_of_resetWord (automaton P)
    (prefix_dPower_isResetWord P hcoprime preword depth
      hdepthPos hdepth hprefix)
  simpa [DFA.cernyBound] using hlength

end DFA.CycleTree
