module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AbnAbStarPowPredN
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

@[expose]
public section

/-!
# The second intersection witness is context-free

This file gives a context-free grammar for
`abnAbStarPowPredN = {a b^n (a b*)^(n-1) | n >= 1}` and proves that it
generates exactly that shared example language.
-/

open List

public inductive AbnAbStarPowPredNNT where
  | S | C | D
deriving DecidableEq

/-- Context-free grammar for `a b^n (a b*)^(n-1)`, `n >= 1`. -/
@[reducible]
public def grammarAbnAbStarPowPredN : CF_grammar Bool where
  nt := AbnAbStarPowPredNNT
  initial := .S
  rules := [
    (.S, [.terminal false, .terminal true, .nonterminal .C]),
    (.C, [.terminal true, .nonterminal .C, .terminal false, .nonterminal .D]),
    (.C, []),
    (.D, [.terminal true, .nonterminal .D]),
    (.D, [])
  ]

private abbrev BG := grammarAbnAbStarPowPredN
private abbrev bS : symbol Bool AbnAbStarPowPredNNT := .nonterminal .S
private abbrev bC : symbol Bool AbnAbStarPowPredNNT := .nonterminal .C
private abbrev bD : symbol Bool AbnAbStarPowPredNNT := .nonterminal .D
private abbrev ba : symbol Bool AbnAbStarPowPredNNT := .terminal false
private abbrev bb : symbol Bool AbnAbStarPowPredNNT := .terminal true

private def cWord (ns : List Nat) : List Bool :=
  replicate ns.length true ++ varyingBlocks ns

private lemma bStepS : CF_transforms BG [bS] [ba, bb, bC] := by
  exact ⟨(.S, [.terminal false, .terminal true, .nonterminal .C]), [], [],
    by simp, rfl, rfl⟩

private lemma bStepC : CF_transforms BG [bC] [bb, bC, ba, bD] := by
  exact ⟨(.C, [.terminal true, .nonterminal .C, .terminal false, .nonterminal .D]),
    [], [], by simp, rfl, rfl⟩

private lemma bStopC : CF_transforms BG [bC] [] := by
  exact ⟨(.C, []), [], [], by simp, rfl, rfl⟩

private lemma bStepD : CF_transforms BG [bD] [bb, bD] := by
  exact ⟨(.D, [.terminal true, .nonterminal .D]), [], [],
    by simp, rfl, rfl⟩

private lemma bStopD : CF_transforms BG [bD] [] := by
  exact ⟨(.D, []), [], [], by simp, rfl, rfl⟩

private lemma bGenerateD (n : Nat) :
    CF_derives BG [bD] ((replicate n true).map symbol.terminal) := by
  induction n with
  | zero => simpa using CF_deri_of_tran bStopD
  | succ n ih =>
      apply CF_deri_of_tran_deri bStepD
      simpa [replicate_succ] using CF_deri_with_prefix [bb] ih

private lemma bGenerateC (ns : List Nat) :
    CF_derives BG [bC] ((cWord ns).map symbol.terminal) := by
  induction ns using List.reverseRecOn with
  | nil => simpa [cWord, varyingBlocks] using CF_deri_of_tran bStopC
  | append_singleton ns q ih =>
      apply CF_deri_of_tran_deri bStepC
      have hc := CF_deri_with_prefix_and_postfix [bb] [ba, bD] ih
      apply CF_deri_of_deri_deri hc
      have hd := CF_deri_with_prefix
        (bb :: (cWord ns).map symbol.terminal ++ [ba]) (bGenerateD q)
      convert hd using 1 <;>
        simp [cWord, varyingBlocks, abBlock, List.map_append,
          List.append_assoc, replicate_succ]

private lemma abnAbStarPowPredN_subset_grammar :
    abnAbStarPowPredN ≤ CF_language BG := by
  rintro w ⟨n, ns, hn, hlen, rfl⟩
  show CF_generates BG (abBlock n ++ varyingBlocks ns)
  unfold CF_generates CF_generates_str
  apply CF_deri_of_tran_deri bStepS
  have hc := CF_deri_with_prefix [ba, bb] (bGenerateC ns)
  convert hc using 1
  · simp
  · rw [← hlen]
    simp [cWord, abBlock, List.map_append, replicate_succ]

/-! ### Compositional soundness for the context-free grammar -/

private def bSymSem : symbol Bool AbnAbStarPowPredNNT → List Bool → Prop
  | .terminal t, w => w = [t]
  | .nonterminal .S, w => w ∈ abnAbStarPowPredN
  | .nonterminal .C, w => ∃ ns : List Nat, w = cWord ns
  | .nonterminal .D, w => ∃ n : Nat, w = replicate n true

private def bFormSem : List (symbol Bool AbnAbStarPowPredNNT) → List Bool → Prop
  | [], w => w = []
  | x :: xs, w => ∃ u v, bSymSem x u ∧ bFormSem xs v ∧ w = u ++ v

private lemma bFormSem_append (xs ys : List (symbol Bool AbnAbStarPowPredNNT)) (w : List Bool) :
    bFormSem (xs ++ ys) w ↔
      ∃ u v, bFormSem xs u ∧ bFormSem ys v ∧ w = u ++ v := by
  induction xs generalizing w with
  | nil => simp [bFormSem]
  | cons x xs ih =>
      simp only [List.cons_append, bFormSem]
      constructor
      · rintro ⟨p, q, hp, hq, rfl⟩
        obtain ⟨u, v, hu, hv, rfl⟩ := (ih q).mp hq
        exact ⟨p ++ u, v, ⟨p, u, hp, hu, rfl⟩, hv,
          by simp [List.append_assoc]⟩
      · rintro ⟨u, v, ⟨p, q, hp, hq, rfl⟩, hv, rfl⟩
        exact ⟨p, q ++ v, hp, (ih (q ++ v)).mpr ⟨q, v, hq, hv, rfl⟩,
          by simp [List.append_assoc]⟩

@[simp] private lemma bFormSem_singleton
    (x : symbol Bool AbnAbStarPowPredNNT) (w : List Bool) :
    bFormSem [x] w ↔ bSymSem x w := by
  simp [bFormSem]

private lemma bFormSem_terminals (w : List Bool) :
    bFormSem (w.map symbol.terminal) w := by
  induction w with
  | nil => simp [bFormSem]
  | cons x xs ih => exact ⟨[x], xs, rfl, ih, rfl⟩

private lemma bFormSem_context {lhs : symbol Bool AbnAbStarPowPredNNT}
    {rhs u v : List (symbol Bool AbnAbStarPowPredNNT)}
    (hsound : ∀ w, bFormSem rhs w → bSymSem lhs w) {w : List Bool}
    (h : bFormSem (u ++ rhs ++ v) w) :
    bFormSem (u ++ [lhs] ++ v) w := by
  rw [List.append_assoc] at h
  obtain ⟨wu, wrv, hu, hrv, rfl⟩ := (bFormSem_append u (rhs ++ v) w).mp h
  obtain ⟨wr, wv, hr, hv, rfl⟩ := (bFormSem_append rhs v wrv).mp hrv
  rw [List.append_assoc]
  apply (bFormSem_append u ([lhs] ++ v) _).mpr
  refine ⟨wu, wr ++ wv, hu, ?_, by simp⟩
  exact (bFormSem_append [lhs] v _).mpr
    ⟨wr, wv, bFormSem_singleton lhs wr |>.mpr (hsound wr hr), hv, rfl⟩

private lemma bRuleSound
    (r : AbnAbStarPowPredNNT × List (symbol Bool AbnAbStarPowPredNNT))
    (hr : r ∈ BG.rules) (w : List Bool) (h : bFormSem r.2 w) :
    bSymSem (.nonterminal r.1) w := by
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have h' : bFormSem [ba, bb, bC] w := h
    obtain ⟨u, rest, hu, hrest, rfl⟩ :=
      (bFormSem_append [ba] [bb, bC] w).mp h'
    obtain ⟨v, z, hv, hz, rfl⟩ :=
      (bFormSem_append [bb] [bC] rest).mp hrest
    rw [bFormSem_singleton] at hu hv hz
    change u = [false] at hu
    change v = [true] at hv
    change ∃ ns, z = cWord ns at hz
    subst u
    subst v
    rcases hz with ⟨ns, rfl⟩
    change [false] ++ ([true] ++ cWord ns) ∈ abnAbStarPowPredN
    refine ⟨ns.length + 1, ns, Nat.zero_lt_succ _, rfl, ?_⟩
    simp [cWord, abBlock, replicate_succ]
  · have h' : bFormSem [bb, bC, ba, bD] w := h
    obtain ⟨u, rest, hu, hrest, rfl⟩ :=
      (bFormSem_append [bb] [bC, ba, bD] w).mp h'
    obtain ⟨v, rest', hv, hrest', rfl⟩ :=
      (bFormSem_append [bC] [ba, bD] rest).mp hrest
    obtain ⟨x, y, hx, hy, rfl⟩ :=
      (bFormSem_append [ba] [bD] rest').mp hrest'
    rw [bFormSem_singleton] at hu hv hx hy
    change u = [true] at hu
    change ∃ ns, v = cWord ns at hv
    change x = [false] at hx
    change ∃ q, y = replicate q true at hy
    subst u
    subst x
    rcases hv with ⟨ns, rfl⟩
    rcases hy with ⟨q, rfl⟩
    refine ⟨ns ++ [q], ?_⟩
    simp [cWord, varyingBlocks, abBlock, replicate_succ, List.append_assoc]
  · have hw : w = [] := by simpa [bFormSem] using h
    subst w
    exact ⟨[], by simp [cWord, varyingBlocks]⟩
  · have h' : bFormSem [bb, bD] w := h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (bFormSem_append [bb] [bD] w).mp h'
    rw [bFormSem_singleton] at hu hv
    change u = [true] at hu
    change ∃ n, v = replicate n true at hv
    subst u
    rcases hv with ⟨n, rfl⟩
    exact ⟨n + 1, by simp [replicate_succ]⟩
  · have hw : w = [] := by simpa [bFormSem] using h
    subst w
    exact ⟨0, rfl⟩

private lemma bTransforms_sound {x y : List (symbol Bool AbnAbStarPowPredNNT)}
    (hxy : CF_transforms BG x y) {w : List Bool} (hy : bFormSem y w) :
    bFormSem x w := by
  rcases hxy with ⟨r, u, v, hr, rfl, rfl⟩
  exact bFormSem_context (fun z hz => bRuleSound r hr z hz) hy

private lemma bDerives_sound {x y : List (symbol Bool AbnAbStarPowPredNNT)}
    (hxy : CF_derives BG x y)
    {w : List Bool} (hy : bFormSem y w) : bFormSem x w := by
  induction hxy with
  | refl => exact hy
  | tail _ ht ih => exact ih (bTransforms_sound ht hy)

private lemma grammar_subset_abnAbStarPowPredN :
    CF_language BG ≤ abnAbStarPowPredN := by
  intro w hw
  have hs := bDerives_sound hw (bFormSem_terminals w)
  rw [bFormSem_singleton] at hs
  exact hs

/-- The context-free grammar generates exactly the second witness language. -/
public theorem grammarAbnAbStarPowPredN_language :
    CF_language grammarAbnAbStarPowPredN = abnAbStarPowPredN := by
  exact le_antisymm grammar_subset_abnAbStarPowPredN
    abnAbStarPowPredN_subset_grammar

/-- The language `a b^n (a b*)^(n-1)`, `n >= 1`, is context-free. -/
public theorem abnAbStarPowPredN_is_CF : is_CF abnAbStarPowPredN :=
  is_CF_via_cfg_implies_is_CF
    ⟨grammarAbnAbStarPowPredN, grammarAbnAbStarPowPredN_language⟩
