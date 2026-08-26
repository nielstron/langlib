module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Examples.AbnPowM
import Langlib.Utilities.Tactics

@[expose]
public section

/-!
# The language `{(a b^n)^m | n,m >= 1}` is indexed

An indexed grammar chooses the common `b`-run length on its flag stack and
then copies that stack to an arbitrary positive number of blocks.
-/

open List

/-! ## The indexed grammar for `abnPowM` -/

public inductive AbnPowMNT where
  | S | X | Z | Y | P
deriving DecidableEq

public inductive AbnPowMFlag where
  | count | bottom
deriving DecidableEq

/-- Indexed grammar which chooses a positive common run length and duplicates its stack. -/
@[reducible]
public def grammarAbnPowM : IndexedGrammar Bool where
  nt := AbnPowMNT
  flag := AbnPowMFlag
  initial := .S
  rules := [
    { lhs := .S, consume := none,
      rhs := [.nonterminal .X (some .bottom)] },
    { lhs := .X, consume := none,
      rhs := [.nonterminal .Z (some .count)] },
    { lhs := .Z, consume := none,
      rhs := [.nonterminal .Z (some .count)] },
    { lhs := .Z, consume := none,
      rhs := [.nonterminal .Y none] },
    { lhs := .Y, consume := none,
      rhs := [.nonterminal .Y none, .nonterminal .Y none] },
    { lhs := .Y, consume := none,
      rhs := [.terminal false, .nonterminal .P none] },
    { lhs := .P, consume := some .count,
      rhs := [.terminal true, .nonterminal .P none] },
    { lhs := .P, consume := some .bottom, rhs := [] }
  ]

private abbrev AG := grammarAbnPowM
private abbrev aS (s : List AbnPowMFlag) : AG.ISym := .indexed .S s
private abbrev aX (s : List AbnPowMFlag) : AG.ISym := .indexed .X s
private abbrev aZ (s : List AbnPowMFlag) : AG.ISym := .indexed .Z s
private abbrev aY (s : List AbnPowMFlag) : AG.ISym := .indexed .Y s
private abbrev aP (s : List AbnPowMFlag) : AG.ISym := .indexed .P s
private abbrev aa : AG.ISym := .terminal false
private abbrev ab : AG.ISym := .terminal true

private def aStack (n : Nat) : List AbnPowMFlag :=
  replicate n .count ++ [.bottom]

@[simp] private lemma aStack_zero : aStack 0 = [.bottom] := by simp [aStack]

private lemma aStack_succ (n : Nat) : aStack (n + 1) = .count :: aStack n := by
  simp [aStack, replicate_succ]

private lemma aStepS : AG.Transforms [aS []] [aX (aStack 0)] := by
  refine ⟨⟨.S, none, [.nonterminal .X (some .bottom)]⟩, [], [], [], ?_, rfl, ?_⟩
  · simp
  · simp [IndexedGrammar.expandRhs, aStack]

private lemma aStepX : AG.Transforms [aX (aStack 0)] [aZ (aStack 1)] := by
  refine ⟨⟨.X, none, [.nonterminal .Z (some .count)]⟩,
    [], [], aStack 0, ?_, rfl, ?_⟩
  · simp
  · simp [IndexedGrammar.expandRhs, aStack, replicate_succ]

private lemma aPushZ (n : Nat) :
    AG.Transforms [aZ (aStack n)] [aZ (aStack (n + 1))] := by
  refine ⟨⟨.Z, none, [.nonterminal .Z (some .count)]⟩,
    [], [], aStack n, ?_, rfl, ?_⟩
  · simp
  · simp [IndexedGrammar.expandRhs, aStack_succ]

private lemma aPushZMany (n : Nat) :
    AG.Derives [aZ (aStack 1)] [aZ (aStack (n + 1))] := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail (aPushZ (n + 1))

private lemma aStepZY (n : Nat) :
    AG.Transforms [aZ (aStack n)] [aY (aStack n)] := by
  refine ⟨⟨.Z, none, [.nonterminal .Y none]⟩, [], [], aStack n, ?_, rfl, ?_⟩
  · simp
  · simp [IndexedGrammar.expandRhs]

private lemma aSplitY (n k : Nat) :
    AG.Derives [aY (aStack n)] (replicate (k + 1) (aY (aStack n))) := by
  induction k with
  | zero => simp; exact Relation.ReflTransGen.refl
  | succ k ih =>
      apply IndexedGrammar.deri_of_tran_deri
      · refine ⟨⟨.Y, none, [.nonterminal .Y none, .nonterminal .Y none]⟩,
          [], [], aStack n, ?_, rfl, rfl⟩
        · simp
      · convert IndexedGrammar.deri_with_prefix [aY (aStack n)] ih using 1 <;>
          simp [IndexedGrammar.expandRhs, replicate_succ]

private lemma aConsumeP (n : Nat) :
    AG.Derives [aP (aStack n)] (replicate n ab) := by
  induction n with
  | zero =>
      exact Relation.ReflTransGen.single ⟨⟨.P, some .bottom, []⟩, [], [], [], by
        simp, by simp [aStack], by
        simp [IndexedGrammar.expandRhs]⟩
  | succ n ih =>
      apply IndexedGrammar.deri_of_tran_deri
      · refine ⟨⟨.P, some .count, [.terminal true, .nonterminal .P none]⟩,
          [], [], aStack n, ?_, ?_, rfl⟩
        · simp
        · simp [aStack_succ]
      · convert IndexedGrammar.deri_with_prefix [ab] ih using 1 <;>
          simp [IndexedGrammar.expandRhs, replicate_succ]

private lemma aGenerateBlock (n : Nat) :
    AG.Derives [aY (aStack n)] ((abBlock n).map IndexedGrammar.ISym.terminal) := by
  apply IndexedGrammar.deri_of_tran_deri
  · refine ⟨⟨.Y, none, [.terminal false, .nonterminal .P none]⟩,
      [], [], aStack n, ?_, rfl, rfl⟩
    · simp
  · convert IndexedGrammar.deri_with_prefix [aa] (aConsumeP n) using 1 <;>
      simp [IndexedGrammar.expandRhs, abBlock]

private lemma aGenerateBlocks (n m : Nat) :
    AG.Derives (replicate m (aY (aStack n)))
      ((blockPower n m).map IndexedGrammar.ISym.terminal) := by
  induction m with
  | zero => simp; exact Relation.ReflTransGen.refl
  | succ m ih =>
      rw [replicate_succ, blockPower_succ, List.map_append]
      exact IndexedGrammar.deri_of_deri_deri
        (IndexedGrammar.deri_with_suffix (replicate m (aY (aStack n))) (aGenerateBlock n))
        (IndexedGrammar.deri_with_prefix
          ((abBlock n).map IndexedGrammar.ISym.terminal) ih)

private lemma abnPowM_subset_grammar :
    abnPowM ≤ AG.Language := by
  rintro w ⟨n, m, hn, hm, rfl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  show AG.Generates (blockPower (n + 1) (m + 1))
  unfold IndexedGrammar.Generates
  exact IndexedGrammar.deri_of_tran_deri aStepS <|
    IndexedGrammar.deri_of_tran_deri aStepX <|
    IndexedGrammar.deri_of_deri_deri (aPushZMany n) <|
    IndexedGrammar.deri_of_tran_deri (aStepZY (n + 1)) <|
    IndexedGrammar.deri_of_deri_deri (aSplitY (n + 1) m) <|
    aGenerateBlocks (n + 1) (m + 1)

/-! ### A compositional soundness interpretation -/

/-- Number of count flags before the first bottom marker. -/
private def aHeight : List AbnPowMFlag → Option Nat
  | [] => none
  | .bottom :: _ => some 0
  | .count :: s => (aHeight s).map Nat.succ

@[simp] private lemma aHeight_bottom (s : List AbnPowMFlag) :
    aHeight (.bottom :: s) = some 0 := rfl

@[simp] private lemma aHeight_count (s : List AbnPowMFlag) :
    aHeight (.count :: s) = (aHeight s).map Nat.succ := rfl

private def aFrom (lower : Nat) (w : List Bool) : Prop :=
  ∃ n m : Nat, lower ≤ n ∧ 0 < m ∧ w = blockPower n m

private def aSymSem : AG.ISym → List Bool → Prop
  | .terminal t, w => w = [t]
  | .indexed .S _, w => aFrom 1 w
  | .indexed .X s, w => ∃ n, aHeight (.count :: s) = some n ∧ aFrom n w
  | .indexed .Z s, w => ∃ n, aHeight s = some n ∧ aFrom n w
  | .indexed .Y s, w =>
      ∃ n m : Nat, aHeight s = some n ∧ 0 < m ∧ w = blockPower n m
  | .indexed .P s, w =>
      ∃ n : Nat, aHeight s = some n ∧ w = replicate n true

private def aFormSem : List AG.ISym → List Bool → Prop
  | [], w => w = []
  | x :: xs, w => ∃ u v, aSymSem x u ∧ aFormSem xs v ∧ w = u ++ v

private lemma aFormSem_append (xs ys : List AG.ISym) (w : List Bool) :
    aFormSem (xs ++ ys) w ↔
      ∃ u v, aFormSem xs u ∧ aFormSem ys v ∧ w = u ++ v := by
  induction xs generalizing w with
  | nil => simp [aFormSem]
  | cons x xs ih =>
      simp only [List.cons_append, aFormSem]
      constructor
      · rintro ⟨p, q, hp, hq, rfl⟩
        obtain ⟨u, v, hu, hv, rfl⟩ := (ih q).mp hq
        exact ⟨p ++ u, v, ⟨p, u, hp, hu, rfl⟩, hv, by simp [List.append_assoc]⟩
      · rintro ⟨u, v, ⟨p, q, hp, hq, rfl⟩, hv, rfl⟩
        exact ⟨p, q ++ v, hp, (ih (q ++ v)).mpr ⟨q, v, hq, hv, rfl⟩,
          by simp [List.append_assoc]⟩

@[simp] private lemma aFormSem_singleton (x : AG.ISym) (w : List Bool) :
    aFormSem [x] w ↔ aSymSem x w := by
  simp [aFormSem]

private lemma aFormSem_terminals (w : List Bool) :
    aFormSem (w.map IndexedGrammar.ISym.terminal) w := by
  induction w with
  | nil => simp [aFormSem]
  | cons x xs ih => exact ⟨[x], xs, rfl, ih, rfl⟩

private lemma aFormSem_context {lhs : AG.ISym} {rhs u v : List AG.ISym}
    (hsound : ∀ w, aFormSem rhs w → aSymSem lhs w) {w : List Bool}
    (h : aFormSem (u ++ rhs ++ v) w) :
    aFormSem (u ++ [lhs] ++ v) w := by
  rw [List.append_assoc] at h
  obtain ⟨wu, wrv, hu, hrv, rfl⟩ := (aFormSem_append u (rhs ++ v) w).mp h
  obtain ⟨wr, wv, hr, hv, rfl⟩ := (aFormSem_append rhs v wrv).mp hrv
  rw [List.append_assoc]
  apply (aFormSem_append u ([lhs] ++ v) _).mpr
  refine ⟨wu, wr ++ wv, hu, ?_, by simp⟩
  exact (aFormSem_append [lhs] v _).mpr
    ⟨wr, wv, aFormSem_singleton lhs wr |>.mpr (hsound wr hr), hv, rfl⟩

private lemma aRuleSound (r : IRule Bool AbnPowMNT AbnPowMFlag)
    (hr : r ∈ AG.rules) (s : List AbnPowMFlag) (w : List Bool)
    (h : aFormSem (AG.expandRhs r.rhs s) w) :
    aSymSem (.indexed r.lhs (match r.consume with | none => s | some f => f :: s)) w := by
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h' : aSymSem (aX (.bottom :: s)) w := by
      exact (aFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change aSymSem (aS s) w
    simpa [aSymSem, aHeight, aFrom] using h'
  · have h' : aSymSem (aZ (.count :: s)) w := by
      exact (aFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change aSymSem (aX s) w
    simpa only [aSymSem] using h'
  · have h' : aSymSem (aZ (.count :: s)) w := by
      exact (aFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change aSymSem (aZ s) w
    simp only [aSymSem] at h' ⊢
    rcases h' with ⟨k, hk, q, m, hq, hm, rfl⟩
    cases hs : aHeight s with
    | none => simp [hs] at hk
    | some j =>
        simp [hs] at hk
        subst k
        exact ⟨j, rfl, q, m, Nat.le_trans (Nat.le_succ j) hq, hm, rfl⟩
  · have h' : aSymSem (aY s) w := by
      exact (aFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change aSymSem (aZ s) w
    simp only [aSymSem] at h' ⊢
    rcases h' with ⟨n, m, hn, hm, rfl⟩
    exact ⟨n, hn, n, m, Nat.le_refl n, hm, rfl⟩
  · have h' : aFormSem [aY s, aY s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (aFormSem_append [aY s] [aY s] w).mp h'
    rw [aFormSem_singleton] at hu hv
    change aSymSem (aY s) (u ++ v)
    change ∃ n m, aHeight s = some n ∧ 0 < m ∧ u = blockPower n m at hu
    change ∃ n m, aHeight s = some n ∧ 0 < m ∧ v = blockPower n m at hv
    rcases hu with ⟨n₁, m₁, hs₁, hm₁, rfl⟩
    rcases hv with ⟨n₂, m₂, hs₂, hm₂, rfl⟩
    have hn : n₁ = n₂ := by simpa [hs₁] using hs₂
    subst n₂
    refine ⟨n₁, m₁ + m₂, hs₁, Nat.add_pos_left hm₁ _, ?_⟩
    exact (blockPower_add n₁ m₁ m₂).symm
  · have h' : aFormSem [aa, aP s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (aFormSem_append [aa] [aP s] w).mp h'
    rw [aFormSem_singleton] at hu hv
    change u = [false] at hu
    change ∃ n, aHeight s = some n ∧ v = replicate n true at hv
    subst u
    rcases hv with ⟨n, hn, rfl⟩
    change aSymSem (aY s) ([false] ++ replicate n true)
    refine ⟨n, 1, hn, Nat.zero_lt_one, ?_⟩
    simp [blockPower, abBlock]
  · have h' : aFormSem [ab, aP s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (aFormSem_append [ab] [aP s] w).mp h'
    rw [aFormSem_singleton] at hu hv
    change u = [true] at hu
    change ∃ n, aHeight s = some n ∧ v = replicate n true at hv
    subst u
    rcases hv with ⟨n, hn, rfl⟩
    change aSymSem (aP (.count :: s)) ([true] ++ replicate n true)
    refine ⟨n + 1, ?_, ?_⟩
    · simp [hn]
    · simp [replicate_succ]
  · have hw : w = [] := by simpa [IndexedGrammar.expandRhs, aFormSem] using h
    subst w
    change aSymSem (aP (.bottom :: s)) []
    exact ⟨0, rfl, rfl⟩

private lemma aTransforms_sound {x y : List AG.ISym} (hxy : AG.Transforms x y)
    {w : List Bool} (hy : aFormSem y w) : aFormSem x w := by
  rcases hxy with ⟨r, u, v, s, hr, hx, rfl⟩
  cases hc : r.consume with
  | none =>
      rw [hc] at hx
      rw [hx]
      exact aFormSem_context (fun z hz => by
        simpa [hc] using aRuleSound r hr s z hz) hy
  | some f =>
      rw [hc] at hx
      rw [hx]
      exact aFormSem_context (fun z hz => by
        simpa [hc] using aRuleSound r hr s z hz) hy

private lemma aDerives_sound {x y : List AG.ISym} (hxy : AG.Derives x y)
    {w : List Bool} (hy : aFormSem y w) : aFormSem x w := by
  induction hxy with
  | refl => exact hy
  | tail _ ht ih => exact ih (aTransforms_sound ht hy)

private lemma grammar_subset_abnPowM :
    AG.Language ≤ abnPowM := by
  intro w hw
  have hs := aDerives_sound hw (aFormSem_terminals w)
  rw [aFormSem_singleton] at hs
  change aSymSem (aS []) w at hs
  change aFrom 1 w at hs
  rcases hs with ⟨n, m, hn, hm, rfl⟩
  exact ⟨n, m, by omega, hm, rfl⟩

/-- The indexed grammar generates exactly the first witness language. -/
public theorem grammarAbnPowM_language :
    grammarAbnPowM.Language = abnPowM := by
  exact le_antisymm grammar_subset_abnPowM
    abnPowM_subset_grammar

/-- The language `{(a b^n)^m | n,m >= 1}` is indexed. -/
public theorem abnPowM_is_Indexed : is_Indexed abnPowM :=
  ⟨grammarAbnPowM, grammarAbnPowM_language⟩
