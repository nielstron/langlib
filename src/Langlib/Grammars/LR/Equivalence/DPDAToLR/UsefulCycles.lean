module

public import Langlib.Automata.DeterministicPushdown.Basics.Determinism
public import Langlib.Automata.DeterministicPushdown.Normalization.FirstFinal

/-!
# Useful cycles in deterministic pushdown computations

A nonempty cycle in a deterministic computation cannot occur before a
configuration from which no step is possible.  The characteristic-grammar
proof uses this elementary fact after two competing active spines have been
projected to the same normalized-DPDA computation.
-/

@[expose]
public section

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem reaches₁_append_stack_exact
    {P : PDA Q T S} {c d : PDA.conf P}
    (h : P.Reaches₁ c d) (suffix : List S) :
    P.Reaches₁ (c.appendStack suffix) (d.appendStack suffix) := by
  rcases c with ⟨q, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with
          ⟨a, tail, next, replacement, rfl, rfl, htransition⟩ |
          ⟨next, replacement, rfl, htransition⟩
      · exact Or.inl ⟨next, replacement, htransition, by
          simp [PDA.conf.appendStack, List.append_assoc]⟩
      · cases input with
        | nil =>
            exact ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩
        | cons a tail =>
            exact Or.inr ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩

private theorem reachesIn_append_stack_exact
    {P : PDA Q T S} {n : ℕ} {c d : PDA.conf P}
    (h : P.ReachesIn n c d) (suffix : List S) :
    P.ReachesIn n (c.appendStack suffix) (d.appendStack suffix) := by
  induction h with
  | refl => exact PDA.ReachesIn.refl _
  | @step n c middle d hprefix hlast ih =>
      exact PDA.ReachesIn.step ih
        (reaches₁_append_stack_exact hlast suffix)

private theorem reachesIn_trans_exact
    {P : PDA Q T S} {n m : ℕ} {a b c : PDA.conf P}
    (hab : P.ReachesIn n a b) (hbc : P.ReachesIn m b c) :
    P.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

private theorem reachesIn_split_exact
    {P : PDA Q T S} {n k : ℕ} {a c : PDA.conf P}
    (h : P.ReachesIn (n + k) a c) :
    ∃ b : PDA.conf P, P.ReachesIn n a b ∧ P.ReachesIn k b c := by
  induction k generalizing c with
  | zero =>
      refine ⟨c, ?_, PDA.ReachesIn.refl c⟩
      simpa using h
  | succ k ih =>
      rw [Nat.add_succ] at h
      obtain ⟨before, hbefore, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr h
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      exact ⟨middle, hprefix,
        PDA.ReachesIn.step hsuffix
          (PDA.reaches₁_iff_reachesIn_one.mpr hlast)⟩

/-- A deterministic run which contains a nonempty cycle cannot later reach a
configuration with no outgoing transition. -/
public theorem toPDA_no_cycle_before_stuck (M : DPDA Q T S)
    {c d : PDA.conf M.toPDA}
    (hcycle : Relation.TransGen
      (@PDA.Reaches₁ Q T S _ _ _ M.toPDA) c c)
    (hreach : M.toPDA.Reaches c d)
    (hstuck : ∀ e : PDA.conf M.toPDA, ¬ M.toPDA.Reaches₁ d e) :
    False := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨e, hstep, _⟩ := Relation.TransGen.head'_iff.mp hcycle
      exact hstuck e hstep
  | @head c middle hstep hrest ih =>
      obtain ⟨cycleNext, hcycleStep, hcycleRest⟩ :=
        Relation.TransGen.head'_iff.mp hcycle
      have hnext : cycleNext = middle :=
        M.toPDA_step_deterministic hcycleStep hstep
      subst cycleNext
      have hcycle' : Relation.TransGen
          (@PDA.Reaches₁ Q T S _ _ _ M.toPDA) middle middle :=
        Relation.TransGen.tail' hcycleRest hstep
      exact ih hcycle'

/-- In particular, a nonempty deterministic cycle cannot have a continuation
to an empty-stack configuration. -/
public theorem toPDA_no_cycle_before_empty_stack (M : DPDA Q T S)
    {c : PDA.conf M.toPDA} {q : Q}
    (hcycle : Relation.TransGen
      (@PDA.Reaches₁ Q T S _ _ _ M.toPDA) c c)
    (hreach : M.toPDA.Reaches c ⟨q, [], []⟩) : False := by
  apply M.toPDA_no_cycle_before_stuck hcycle hreach
  intro e hstep
  simpa [PDA.Reaches₁, PDA.step] using hstep

/-- Two comparable configurations on a useful deterministic run cannot have
distinct one-step edges which merge immediately.  Otherwise the longer
prefix, followed by its edge to the common successor, forms a nonempty cycle
before the successor's empty-stack continuation. -/
public theorem toPDA_predecessor_eq_of_comparable (M : DPDA Q T S)
    {c₁ c₂ next : PDA.conf M.toPDA} {final : Q}
    (hcomparable : M.toPDA.Reaches c₁ c₂ ∨
      M.toPDA.Reaches c₂ c₁)
    (hstep₁ : M.toPDA.Reaches₁ c₁ next)
    (hstep₂ : M.toPDA.Reaches₁ c₂ next)
    (huseful : M.toPDA.Reaches next ⟨final, [], []⟩) :
    c₁ = c₂ := by
  rcases hcomparable with h₁₂ | h₂₁
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h₁₂ with
        heq | hstrict
    · exact heq.symm
    · obtain ⟨after, hfirst, hrest⟩ :=
        Relation.TransGen.head'_iff.mp hstrict
      have hafter : after = next :=
        M.toPDA_step_deterministic hfirst hstep₁
      subst after
      have hcycle : Relation.TransGen
          (@PDA.Reaches₁ Q T S _ _ _ M.toPDA) next next :=
        Relation.TransGen.tail' hrest hstep₂
      exact False.elim (M.toPDA_no_cycle_before_empty_stack hcycle huseful)
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h₂₁ with
        heq | hstrict
    · exact heq
    · obtain ⟨after, hfirst, hrest⟩ :=
        Relation.TransGen.head'_iff.mp hstrict
      have hafter : after = next :=
        M.toPDA_step_deterministic hfirst hstep₂
      subst after
      have hcycle : Relation.TransGen
          (@PDA.Reaches₁ Q T S _ _ _ M.toPDA) next next :=
        Relation.TransGen.tail' hrest hstep₁
      exact False.elim (M.toPDA_no_cycle_before_empty_stack hcycle huseful)

/-- A deterministic pushdown computation cannot usefully repeat a stack
growth segment.  The segment starts and ends with the same state and exposed
stack prefix, inserting a nonempty block immediately below that prefix.  By
stack locality it can be repeated arbitrarily often; determinism would then
place an arbitrarily long growth run before a fixed finite empty-stack
continuation. -/
public theorem toPDA_no_useful_stack_growth (M : DPDA Q T S)
    {q final : Q} {base extra context : List S} {input : List T}
    (hgrowth : M.toPDA.Reaches
      ⟨q, [], base⟩ ⟨q, [], base ++ extra⟩)
    (hextra : extra ≠ [])
    (huseful : M.toPDA.Reaches
      ⟨q, input, base ++ extra ++ context⟩ ⟨final, [], []⟩) :
    False := by
  rw [PDA.reaches_iff_reachesIn] at hgrowth huseful
  obtain ⟨m, hm⟩ := hgrowth
  obtain ⟨n, hn⟩ := huseful
  have hmpos : 0 < m := by
    by_contra hnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hnot
    subst m
    have hsame := PDA.reachesIn_zero hm
    have hlength := congrArg (fun c : PDA.conf M.toPDA => c.stack.length) hsame
    simp only [List.length_append] at hlength
    have : extra.length = 0 := by omega
    exact hextra (List.length_eq_zero_iff.mp this)
  let blocks : ℕ → List S := fun k => (List.replicate k extra).flatten
  have hrepeat : ∀ k : ℕ,
      M.toPDA.ReachesIn (k * m)
        ⟨q, input, base ++ extra ++ context⟩
        ⟨q, input, base ++ blocks (k + 1) ++ context⟩ := by
    intro k
    induction k with
    | zero =>
        simpa [blocks] using
          (PDA.ReachesIn.refl
            (⟨q, input, base ++ extra ++ context⟩ :
              PDA.conf M.toPDA))
    | succ k ih =>
        have hgrowthInput : M.toPDA.ReachesIn m
            ⟨q, input, base⟩
            ⟨q, input, base ++ extra⟩ := by
          simpa [PDA.conf.appendInput] using
            (PDA.unconsumed_input_N (pda := M.toPDA) input).mp hm
        have hnext := reachesIn_append_stack_exact hgrowthInput
          (blocks (k + 1) ++ context)
        have hnext' : M.toPDA.ReachesIn m
            ⟨q, input, base ++ blocks (k + 1) ++ context⟩
            ⟨q, input, base ++ blocks (k + 2) ++ context⟩ := by
          simpa [blocks, PDA.conf.appendStack, List.replicate_succ,
            List.append_assoc] using hnext
        simpa [Nat.succ_mul, Nat.add_assoc] using
          reachesIn_trans_exact ih hnext'
  have hmone : 1 ≤ m := hmpos
  have hnle : n ≤ (n + 1) * m := by
    have hmul := Nat.mul_le_mul_left (n + 1) hmone
    omega
  have hpast := M.toPDA_reachesIn_prefix_of_le hnle hn (hrepeat (n + 1))
  have hempty := PDA.reaches_on_empty_stack hpast
  have hstack : base ++ blocks (n + 1 + 1) ++ context = [] := hempty.2.1
  have hleft : base ++ blocks (n + 1 + 1) = [] :=
    (List.append_eq_nil_iff.mp hstack).1
  have hblocks : blocks (n + 1 + 1) = [] :=
    (List.append_eq_nil_iff.mp hleft).2
  have hlength := congrArg List.length hblocks
  simp [blocks, List.replicate_succ] at hlength
  exact hextra hlength.1

/-- First-final normalization also rules out a repeatable stack-growth
segment before a normalized final state, even if the stack has not yet been
drained.  A sufficiently long repetition contains the finite path to that
final state as a prefix.  The first-final marker then either was already set,
or is set on leaving the final state, and in either case cannot return to the
unchanged source state of the repeated segment. -/
public theorem firstFinal_toPDA_no_stack_growth_before_final
    (M : DPDA Q T S)
    {q p : Q × Bool} {base extra context targetStack : List S}
    {input output : List T}
    (hgrowth : M.firstFinal.toPDA.Reaches
      ⟨q, [], base⟩ ⟨q, [], base ++ extra⟩)
    (hextra : extra ≠ [])
    (hreach : M.firstFinal.toPDA.Reaches
      ⟨q, input, base ++ extra ++ context⟩
      ⟨p, output, targetStack⟩)
    (hfinal : p ∈ M.firstFinal.final_states) : False := by
  rw [PDA.reaches_iff_reachesIn] at hgrowth hreach
  obtain ⟨m, hm⟩ := hgrowth
  obtain ⟨n, hn⟩ := hreach
  have hmpos : 0 < m := by
    by_contra hnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hnot
    subst m
    have hsame := PDA.reachesIn_zero hm
    have hlength := congrArg
      (fun c : PDA.conf M.firstFinal.toPDA => c.stack.length) hsame
    simp only [List.length_append] at hlength
    have : extra.length = 0 := by omega
    exact hextra (List.length_eq_zero_iff.mp this)
  let blocks : ℕ → List S := fun k => (List.replicate k extra).flatten
  have hrepeat : ∀ k : ℕ,
      M.firstFinal.toPDA.ReachesIn (k * m)
        ⟨q, input, base ++ extra ++ context⟩
        ⟨q, input, base ++ blocks (k + 1) ++ context⟩ := by
    intro k
    induction k with
    | zero =>
        simpa [blocks] using
          (PDA.ReachesIn.refl
            (⟨q, input, base ++ extra ++ context⟩ :
              PDA.conf M.firstFinal.toPDA))
    | succ k ih =>
        have hgrowthInput : M.firstFinal.toPDA.ReachesIn m
            ⟨q, input, base⟩
            ⟨q, input, base ++ extra⟩ := by
          simpa [PDA.conf.appendInput] using
            (PDA.unconsumed_input_N
              (pda := M.firstFinal.toPDA) input).mp hm
        have hnext := reachesIn_append_stack_exact hgrowthInput
          (blocks (k + 1) ++ context)
        have hnext' : M.firstFinal.toPDA.ReachesIn m
            ⟨q, input, base ++ blocks (k + 1) ++ context⟩
            ⟨q, input, base ++ blocks (k + 2) ++ context⟩ := by
          simpa [blocks, PDA.conf.appendStack, List.replicate_succ,
            List.append_assoc] using hnext
        simpa [Nat.succ_mul, Nat.add_assoc] using
          reachesIn_trans_exact ih hnext'
  let total := (n + 1) * m
  have hntotal : n < total := by
    dsimp [total]
    have hmone : 1 ≤ m := hmpos
    have hmul := Nat.mul_le_mul_left (n + 1) hmone
    omega
  obtain ⟨k, htotal⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hntotal)
  have hlong : M.firstFinal.toPDA.ReachesIn total
      ⟨q, input, base ++ extra ++ context⟩
      ⟨q, input, base ++ blocks (n + 1 + 1) ++ context⟩ := by
    simpa [total] using hrepeat (n + 1)
  rw [htotal] at hlong
  obtain ⟨middle, hprefix, hsuffix⟩ :=
    reachesIn_split_exact hlong
  have hmiddle : middle =
      (⟨p, output, targetStack⟩ : PDA.conf M.firstFinal.toPDA) :=
    M.firstFinal.toPDA_reachesIn_deterministic hprefix hn
  subst middle
  have hkpos : 0 < k := by omega
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hkpos)
  obtain ⟨after, hfirst, hrest⟩ :=
    PDA.reachesIn_iff_split_first.mpr hsuffix
  have hafter : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
      ⟨p, output, targetStack⟩
      ⟨q, input, base ++ blocks (n + 1 + 1) ++ context⟩ :=
    Relation.TransGen.head'
      (PDA.reaches₁_iff_reachesIn_one.mpr hfirst)
      (PDA.reaches_of_reachesIn hrest)
  exact M.firstFinal_no_return_through_final
    (PDA.reaches_of_reachesIn hn) hfinal hafter

end DPDA
