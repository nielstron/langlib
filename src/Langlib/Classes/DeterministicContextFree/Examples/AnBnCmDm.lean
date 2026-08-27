module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Examples.AnBnCmDm
import Langlib.Classes.ContextFree.Examples.AnBnCmDm
import Mathlib.Tactic

@[expose]
public section

/-! # `{0ⁿ1ⁿ2ᵐ3ᵐ}` is deterministic context-free

The two balanced blocks use disjoint letters, so a deterministic pushdown
automaton can empty and reuse its stack at their visible boundary.
-/

open PDA List

namespace DCFAnBnCmDm

public inductive State where
  | start
  | readA
  | readB
  | between
  | readC
  | readD
  | done
deriving DecidableEq

public instance : Fintype State :=
  Fintype.ofList [.start, .readA, .readB, .between, .readC, .readD, .done]
    (by intro q; cases q <;> simp)

public inductive Stack where
  | bottom
  | mark
deriving DecidableEq

public instance : Fintype Stack :=
  Fintype.ofList [.bottom, .mark] (by intro Z; cases Z <;> simp)

open State Stack

/-- A DPDA for `{0ⁿ1ⁿ2ᵐ3ᵐ}`.  States `start`, `between`, and `done`
accept respectively the empty word, a completed first block, and both blocks. -/
public def dpda : DPDA State (Fin 4) Stack where
  initial_state := start
  start_symbol := bottom
  final_states := {start, between, done}
  transition q x Z :=
    match q, Z with
    | start, bottom =>
        if x = 0 then some (readA, [mark, bottom])
        else if x = 2 then some (readC, [mark, bottom])
        else none
    | readA, mark =>
        if x = 0 then some (readA, [mark, mark])
        else if x = 1 then some (readB, [])
        else none
    | readB, mark =>
        if x = 1 then some (readB, []) else none
    | between, bottom =>
        if x = 2 then some (readC, [mark, bottom]) else none
    | readC, mark =>
        if x = 2 then some (readC, [mark, mark])
        else if x = 3 then some (readD, [])
        else none
    | readD, mark =>
        if x = 3 then some (readD, []) else none
    | _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | readB, bottom => some (between, [bottom])
    | readD, bottom => some (done, [bottom])
    | _, _ => none
  no_mixed := by decide

private lemma step_start_a (rest : List (Fin 4)) :
    dpda.toPDA.Reaches₁ ⟨start, 0 :: rest, [bottom]⟩
      ⟨readA, rest, [mark, bottom]⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_start_c (rest : List (Fin 4)) :
    dpda.toPDA.Reaches₁ ⟨start, 2 :: rest, [bottom]⟩
      ⟨readC, rest, [mark, bottom]⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_a (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readA, 0 :: rest, mark :: stk⟩
      ⟨readA, rest, mark :: mark :: stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_b_first (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readA, 1 :: rest, mark :: stk⟩
      ⟨readB, rest, stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_b (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readB, 1 :: rest, mark :: stk⟩
      ⟨readB, rest, stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_between (rest : List (Fin 4)) :
    dpda.toPDA.Reaches₁ ⟨readB, rest, [bottom]⟩
      ⟨between, rest, [bottom]⟩ := by
  cases rest with
  | nil =>
      unfold PDA.Reaches₁ PDA.step
      exact ⟨between, [bottom], Set.mem_singleton _, rfl⟩
  | cons a rest =>
      unfold PDA.Reaches₁ PDA.step
      exact Set.mem_union_right _ ⟨between, [bottom], Set.mem_singleton _, rfl⟩

private lemma step_between_c (rest : List (Fin 4)) :
    dpda.toPDA.Reaches₁ ⟨between, 2 :: rest, [bottom]⟩
      ⟨readC, rest, [mark, bottom]⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_c (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readC, 2 :: rest, mark :: stk⟩
      ⟨readC, rest, mark :: mark :: stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_d_first (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readC, 3 :: rest, mark :: stk⟩
      ⟨readD, rest, stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_d (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches₁ ⟨readD, 3 :: rest, mark :: stk⟩
      ⟨readD, rest, stk⟩ := by
  constructor
  unfold dpda
  aesop

private lemma step_done :
    dpda.toPDA.Reaches₁ ⟨readD, [], [bottom]⟩
      ⟨done, [], [bottom]⟩ := by
  constructor
  unfold dpda
  aesop

private lemma push_as (n : ℕ) (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches
      ⟨readA, replicate n 0 ++ rest, mark :: stk⟩
      ⟨readA, rest, replicate (n + 1) mark ++ stk⟩ := by
  induction n generalizing stk with
  | zero => exact .refl _
  | succ n ih =>
      have hfirst := Relation.ReflTransGen.single
        (step_a (replicate n 0 ++ rest) stk)
      have hrest := ih (mark :: stk)
      have hstack : replicate (n + 1) mark ++ mark :: stk =
          replicate (n.succ + 1) mark ++ stk := by
        have hrepl : replicate (n.succ + 1) mark =
            replicate (n + 1) mark ++ [mark] := by
          rw [show n.succ + 1 = (n + 1) + 1 by omega, List.replicate_succ']
        rw [hrepl, List.append_assoc]
        rfl
      have hinput : replicate n.succ (0 : Fin 4) ++ rest =
          0 :: (replicate n 0 ++ rest) := by simp [List.replicate_succ]
      rw [hinput, ← hstack]
      exact hfirst.trans hrest

private lemma pop_bs (n : ℕ) (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches
      ⟨readB, replicate n 1 ++ rest, replicate n mark ++ stk⟩
      ⟨readB, rest, stk⟩ := by
  induction n generalizing stk with
  | zero => simp; exact .refl _
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        (PDA.Reaches.trans (.single (step_b (replicate n 1 ++ rest)
          (replicate n mark ++ stk))) (ih stk))

private lemma push_cs (n : ℕ) (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches
      ⟨readC, replicate n 2 ++ rest, mark :: stk⟩
      ⟨readC, rest, replicate (n + 1) mark ++ stk⟩ := by
  induction n generalizing stk with
  | zero => exact .refl _
  | succ n ih =>
      have hfirst := Relation.ReflTransGen.single
        (step_c (replicate n 2 ++ rest) stk)
      have hrest := ih (mark :: stk)
      have hstack : replicate (n + 1) mark ++ mark :: stk =
          replicate (n.succ + 1) mark ++ stk := by
        have hrepl : replicate (n.succ + 1) mark =
            replicate (n + 1) mark ++ [mark] := by
          rw [show n.succ + 1 = (n + 1) + 1 by omega, List.replicate_succ']
        rw [hrepl, List.append_assoc]
        rfl
      have hinput : replicate n.succ (2 : Fin 4) ++ rest =
          2 :: (replicate n 2 ++ rest) := by simp [List.replicate_succ]
      rw [hinput, ← hstack]
      exact hfirst.trans hrest

private lemma pop_ds (n : ℕ) (rest : List (Fin 4)) (stk : List Stack) :
    dpda.toPDA.Reaches
      ⟨readD, replicate n 3 ++ rest, replicate n mark ++ stk⟩
      ⟨readD, rest, stk⟩ := by
  induction n generalizing stk with
  | zero => simp; exact .refl _
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        (PDA.Reaches.trans (.single (step_d (replicate n 3 ++ rest)
          (replicate n mark ++ stk))) (ih stk))

private lemma complete (n m : ℕ) :
    replicate n 0 ++ replicate n 1 ++ replicate m 2 ++ replicate m 3 ∈
      dpda.acceptsByFinalState := by
  rcases n with _ | n
  · rcases m with _ | m
    · exact ⟨start, by simp [dpda], [bottom], .refl _⟩
    · refine ⟨done, by simp [dpda], [bottom], ?_⟩
      have h₁ := Relation.ReflTransGen.single (step_start_c
        (replicate m 2 ++ replicate (m + 1) 3))
      have h₂ := push_cs m (replicate (m + 1) 3) [bottom]
      have h₃ := Relation.ReflTransGen.single
        (step_d_first (replicate m 3) (replicate m mark ++ [bottom]))
      have h₄ : dpda.toPDA.Reaches
          ⟨readD, replicate m 3, replicate m mark ++ [bottom]⟩
          ⟨readD, [], [bottom]⟩ := by simpa using pop_ds m [] [bottom]
      simpa [List.replicate_succ, List.append_assoc, dpda, DPDA.toPDA] using
        h₁.trans (h₂.trans (h₃.trans (h₄.trans (.single step_done))))
  · have firstDone (tail : List (Fin 4)) : dpda.toPDA.Reaches
        ⟨start, replicate (n + 1) 0 ++ replicate (n + 1) 1 ++ tail, [bottom]⟩
        ⟨between, tail, [bottom]⟩ := by
      have h₁ := Relation.ReflTransGen.single (step_start_a
        (replicate n 0 ++ replicate (n + 1) 1 ++ tail))
      have h₂ : dpda.toPDA.Reaches
          ⟨readA, replicate n 0 ++ replicate (n + 1) 1 ++ tail, [mark, bottom]⟩
          ⟨readA, replicate (n + 1) 1 ++ tail,
            replicate (n + 1) mark ++ [bottom]⟩ := by
        simpa only [List.append_assoc] using
          push_as n (replicate (n + 1) 1 ++ tail) [bottom]
      have h₃ := Relation.ReflTransGen.single
        (step_b_first (replicate n 1 ++ tail) (replicate n mark ++ [bottom]))
      have h₄ : dpda.toPDA.Reaches
          ⟨readB, replicate n 1 ++ tail, replicate n mark ++ [bottom]⟩
          ⟨readB, tail, [bottom]⟩ := pop_bs n tail [bottom]
      have h₅ : dpda.toPDA.Reaches ⟨readB, tail, [bottom]⟩
          ⟨between, tail, [bottom]⟩ := .single (step_between tail)
      simpa [List.replicate_succ, List.append_assoc] using
        h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
    rcases m with _ | m
    · refine ⟨between, by simp [dpda], [bottom], ?_⟩
      simpa only [List.replicate_zero, List.append_nil, dpda, DPDA.toPDA] using
        firstDone []
    · refine ⟨done, by simp [dpda], [bottom], ?_⟩
      have h₀ := firstDone (replicate (m + 1) 2 ++ replicate (m + 1) 3)
      have h₁ := Relation.ReflTransGen.single (step_between_c
        (replicate m 2 ++ replicate (m + 1) 3))
      have h₂ := push_cs m (replicate (m + 1) 3) [bottom]
      have h₃ := Relation.ReflTransGen.single
        (step_d_first (replicate m 3) (replicate m mark ++ [bottom]))
      have h₄ : dpda.toPDA.Reaches
          ⟨readD, replicate m 3, replicate m mark ++ [bottom]⟩
          ⟨readD, [], [bottom]⟩ := by simpa using pop_ds m [] [bottom]
      simpa [List.replicate_succ, List.append_assoc, dpda, DPDA.toPDA] using
        h₀.trans (h₁.trans (h₂.trans (h₃.trans
          (h₄.trans (.single step_done)))))

private def Inv (w : List (Fin 4)) (c : dpda.toPDA.conf) : Prop :=
  ∃ na nb nc nd : ℕ,
    w = replicate na 0 ++ replicate nb 1 ++ replicate nc 2 ++ replicate nd 3 ++ c.input ∧
    ((c.state = start ∧ na = 0 ∧ nb = 0 ∧ nc = 0 ∧ nd = 0 ∧
        c.stack = [bottom]) ∨
     (c.state = readA ∧ 1 ≤ na ∧ nb = 0 ∧ nc = 0 ∧ nd = 0 ∧
        c.stack = replicate na mark ++ [bottom]) ∨
     (c.state = readB ∧ 1 ≤ nb ∧ nb ≤ na ∧ nc = 0 ∧ nd = 0 ∧
        c.stack = replicate (na - nb) mark ++ [bottom]) ∨
     (c.state = between ∧ nb = na ∧ nc = 0 ∧ nd = 0 ∧
        c.stack = [bottom]) ∨
     (c.state = readC ∧ nb = na ∧ 1 ≤ nc ∧ nd = 0 ∧
        c.stack = replicate nc mark ++ [bottom]) ∨
     (c.state = readD ∧ nb = na ∧ 1 ≤ nd ∧ nd ≤ nc ∧
        c.stack = replicate (nc - nd) mark ++ [bottom]) ∨
     (c.state = done ∧ nb = na ∧ nd = nc ∧ c.stack = [bottom]))

private lemma inv_step (w : List (Fin 4)) (c c' : dpda.toPDA.conf)
    (hinv : Inv w c) (hstep : dpda.toPDA.Reaches₁ c c') : Inv w c' := by
  rcases c with ⟨q, input, stack⟩
  obtain ⟨na, nb, nc, nd, hw, hcases⟩ := hinv
  dsimp at hw hcases hstep
  rcases hcases with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, hna, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, hnb1, hnbna, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, hnc, rfl, rfl⟩ |
    ⟨rfl, rfl, hnd1, hndnc, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    try simp only [List.replicate_zero, List.nil_append] at hw
  · rcases input with _ | ⟨x, rest⟩
    · obtain ⟨p, β, hpβ, rfl⟩ := hstep
      simp_all +decide [dpda]
    · fin_cases x
      · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
        · have hp : p = readA ∧ β = [mark, bottom] := by
            simpa +decide [dpda, DPDA.toPDA] using hpβ
          rcases hp with ⟨rfl, rfl⟩
          refine ⟨1, 0, 0, 0, ?_, ?_⟩
          · simpa using hw
          · exact Or.inr <| Or.inl ⟨rfl, by omega, rfl, rfl, rfl, rfl⟩
        · simp_all +decide [dpda]
      · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
          simp_all +decide [dpda]
      · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
        · have hp : p = readC ∧ β = [mark, bottom] := by
            simpa +decide [dpda, DPDA.toPDA] using hpβ
          rcases hp with ⟨rfl, rfl⟩
          refine ⟨0, 0, 1, 0, ?_, ?_⟩
          · simpa using hw
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inl ⟨rfl, rfl, by omega, rfl, rfl⟩
        · simp_all +decide [dpda]
      · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
          simp_all +decide [dpda]
  · cases na with
    | zero => omega
    | succ k =>
        simp only [List.replicate_succ, List.cons_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            simp_all +decide [dpda]
        | cons x rest =>
            fin_cases x
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readA ∧ β = [mark, mark] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨k + 2, 0, 0, 0, ?_, ?_⟩
                · have hrepl : replicate (k + 2) (0 : Fin 4) =
                      replicate (k + 1) 0 ++ [0] := by
                    rw [show k + 2 = (k + 1) + 1 by omega, List.replicate_succ']
                  simpa [hrepl, List.append_assoc] using hw
                · refine Or.inr <| Or.inl ⟨rfl, by omega, rfl, rfl, rfl, ?_⟩
                  simp [show k + 2 = (k + 1) + 1 by omega, List.replicate_succ]
              · simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readB ∧ β = [] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨k + 1, 1, 0, 0, ?_, ?_⟩
                · simpa [List.append_assoc] using hw
                · refine Or.inr <| Or.inr <| Or.inl
                    ⟨rfl, by omega, by omega, rfl, rfl, ?_⟩
                  simp
              · simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
  · cases hdiff : na - nb with
    | zero =>
        have hna : na = nb := by omega
        simp only [hdiff, List.replicate_zero, List.nil_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            have hp : p = between ∧ β = [bottom] := by
              simpa +decide [dpda] using hpβ
            rcases hp with ⟨rfl, rfl⟩
            exact ⟨na, nb, 0, 0, by simpa using hw,
              Or.inr <| Or.inr <| Or.inr <| Or.inl
                ⟨rfl, hna.symm, rfl, rfl, rfl⟩⟩
        | cons x rest =>
            rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
            · simp_all +decide [dpda]
            · have hp : p = between ∧ β = [bottom] := by
                simpa +decide [dpda] using hpβ
              rcases hp with ⟨rfl, rfl⟩
              exact ⟨na, nb, 0, 0, by simpa using hw,
                Or.inr <| Or.inr <| Or.inr <| Or.inl
                  ⟨rfl, hna.symm, rfl, rfl, rfl⟩⟩
    | succ k =>
        simp only [hdiff, List.replicate_succ, List.cons_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            simp_all +decide [dpda]
        | cons x rest =>
            fin_cases x
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readB ∧ β = [] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                have hdiff' : na - (nb + 1) = k := by omega
                refine ⟨na, nb + 1, 0, 0, ?_, ?_⟩
                · have hrepl : replicate (nb + 1) (1 : Fin 4) =
                      replicate nb 1 ++ [1] := by rw [List.replicate_succ']
                  simpa [hrepl, List.append_assoc] using hw
                · refine Or.inr <| Or.inr <| Or.inl
                    ⟨rfl, by omega, by omega, rfl, rfl, ?_⟩
                  simp [hdiff']
              · simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
  · cases input with
    | nil =>
        obtain ⟨p, β, hpβ, rfl⟩ := hstep
        simp_all +decide [dpda]
    | cons x rest =>
        fin_cases x
        · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
            simp_all +decide [dpda]
        · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
            simp_all +decide [dpda]
        · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
          · have hp : p = readC ∧ β = [mark, bottom] := by
              simpa +decide [dpda] using hpβ
            rcases hp with ⟨rfl, rfl⟩
            refine ⟨nb, nb, 1, 0, ?_, ?_⟩
            · simpa [List.append_assoc] using hw
            · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                Or.inl ⟨rfl, rfl, by omega, rfl, rfl⟩
          · simp_all +decide [dpda]
        · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
            simp_all +decide [dpda]
  · cases nc with
    | zero => omega
    | succ k =>
        simp only [List.replicate_succ, List.cons_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            simp_all +decide [dpda]
        | cons x rest =>
            fin_cases x
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readC ∧ β = [mark, mark] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨nb, nb, k + 2, 0, ?_, ?_⟩
                · have hrepl : replicate (k + 2) (2 : Fin 4) =
                      replicate (k + 1) 2 ++ [2] := by
                    rw [show k + 2 = (k + 1) + 1 by omega, List.replicate_succ']
                  simpa [hrepl, List.append_assoc] using hw
                · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                    Or.inl ⟨rfl, rfl, by omega, rfl, ?_⟩
                  simp [show k + 2 = (k + 1) + 1 by omega, List.replicate_succ]
              · simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readD ∧ β = [] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨nb, nb, k + 1, 1, ?_, ?_⟩
                · simpa [List.append_assoc] using hw
                · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                    Or.inl ⟨rfl, rfl, by omega, by omega, ?_⟩
                  simp
              · simp_all +decide [dpda]
  · cases hdiff : nc - nd with
    | zero =>
        have hnc : nc = nd := by omega
        simp only [hdiff, List.replicate_zero, List.nil_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            have hp : p = done ∧ β = [bottom] := by
              simpa +decide [dpda] using hpβ
            rcases hp with ⟨rfl, rfl⟩
            exact ⟨nb, nb, nc, nd, by simpa using hw,
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                ⟨rfl, rfl, hnc.symm, rfl⟩⟩
        | cons x rest =>
            rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
            · simp_all +decide [dpda]
            · have hp : p = done ∧ β = [bottom] := by
                simpa +decide [dpda] using hpβ
              rcases hp with ⟨rfl, rfl⟩
              exact ⟨nb, nb, nc, nd, by simpa using hw,
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                  ⟨rfl, rfl, hnc.symm, rfl⟩⟩
    | succ k =>
        simp only [hdiff, List.replicate_succ, List.cons_append] at hstep
        cases input with
        | nil =>
            obtain ⟨p, β, hpβ, rfl⟩ := hstep
            simp_all +decide [dpda]
        | cons x rest =>
            fin_cases x
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
                simp_all +decide [dpda]
            · rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩
              · have hp : p = readD ∧ β = [] := by
                  simpa +decide [dpda] using hpβ
                rcases hp with ⟨rfl, rfl⟩
                have hdiff' : nc - (nd + 1) = k := by omega
                refine ⟨nb, nb, nc, nd + 1, ?_, ?_⟩
                · have hrepl : replicate (nd + 1) (3 : Fin 4) =
                      replicate nd 3 ++ [3] := by rw [List.replicate_succ']
                  simpa [hrepl, List.append_assoc] using hw
                · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                    Or.inl ⟨rfl, rfl, by omega, by omega, ?_⟩
                  simp [hdiff']
              · simp_all +decide [dpda]
  · cases input with
    | nil =>
        obtain ⟨p, β, hpβ, rfl⟩ := hstep
        simp_all +decide [dpda]
    | cons x rest =>
        rcases hstep with ⟨p, β, hpβ, rfl⟩ | ⟨p, β, hpβ, rfl⟩ <;>
          simp_all +decide [dpda]

private lemma inv_reaches (w : List (Fin 4)) (c c' : dpda.toPDA.conf)
    (hinv : Inv w c) (hreach : dpda.toPDA.Reaches c c') : Inv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact inv_step w _ _ ih hstep

private lemma sound (w : List (Fin 4)) (h : w ∈ dpda.acceptsByFinalState) :
    ∃ n m : ℕ,
      w = replicate n 0 ++ replicate n 1 ++ replicate m 2 ++ replicate m 3 := by
  obtain ⟨q, hq, γ, hreach⟩ := h
  obtain ⟨na, nb, nc, nd, hw, hcases⟩ :=
    inv_reaches w
      ⟨dpda.toPDA.initial_state, w, [dpda.toPDA.start_symbol]⟩
      ⟨q, [], γ⟩
      ⟨0, 0, 0, 0, by simp,
        Or.inl ⟨by simp [dpda], rfl, rfl, rfl, rfl, by simp [dpda]⟩⟩
      hreach
  fin_cases q
  · refine ⟨0, 0, ?_⟩
    simp_all +decide [dpda]
  · simp_all +decide [dpda]
  · simp_all +decide [dpda]
  · refine ⟨nb, 0, ?_⟩
    simp_all +decide [dpda]
  · simp_all +decide [dpda]
  · simp_all +decide [dpda]
  · refine ⟨nb, nd, ?_⟩
    simp_all +decide [dpda]

private lemma mem_anbncmdm_iff {w : List (Fin 4)} :
    w ∈ anbncmdm ↔
      ∃ n m : ℕ,
        w = replicate n 0 ++ replicate n 1 ++ replicate m 2 ++ replicate m 3 := by
  constructor
  · rw [anbncmdm, Language.mem_mul]
    rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨n, rfl⟩ := eq_of_mem_map_anbn hu
    obtain ⟨m, rfl⟩ := eq_of_mem_map_anbn hv
    exact ⟨n, m, by simp [f4, g4, List.append_assoc]⟩
  · rintro ⟨n, m, rfl⟩
    rw [anbncmdm, Language.mem_mul]
    refine ⟨replicate n 0 ++ replicate n 1, ?_,
      replicate m 2 ++ replicate m 3, ?_, by simp [List.append_assoc]⟩
    · simpa [f4] using mem_map_anbn f4 n
    · simpa [g4] using mem_map_anbn g4 m

/-- The concrete DPDA accepts exactly `{0ⁿ1ⁿ2ᵐ3ᵐ}`. -/
public theorem dpda_accepts : dpda.acceptsByFinalState = anbncmdm := by
  ext w
  rw [mem_anbncmdm_iff]
  exact ⟨sound w, fun ⟨n, m, hw⟩ => hw ▸ complete n m⟩

/-- `{0ⁿ1ⁿ2ᵐ3ᵐ}` is deterministic context-free. -/
public theorem anbncmdm_is_DCF : is_DCF anbncmdm :=
  ⟨State, Stack, inferInstance, inferInstance, dpda, dpda_accepts⟩

end DCFAnBnCmDm

end
