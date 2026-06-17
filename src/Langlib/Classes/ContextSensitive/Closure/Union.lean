module

public import Langlib.Classes.ContextSensitive.Basics.NonContracting
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Classes.RecursivelyEnumerable.Basics.Lifting
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

/-! # Context-Sensitive Closure Under Union

We prove closure under union by first normalizing each context-sensitive grammar to an
equivalent noncontracting grammar away from `ε`. Noncontracting grammars are closed under
union by adding a fresh start symbol that jumps to either summand. If the original union
contains `ε`, we add it back using the existing `addEmpty` construction.
-/

variable {T : Type}

namespace ContextSensitiveUnion

private inductive UnionNT (N₁ N₂ : Type) where
  | start : UnionNT N₁ N₂
  | left : N₁ → UnionNT N₁ N₂
  | right : N₂ → UnionNT N₁ N₂

private def unionStartLeft (g₁ g₂ : grammar T) :
    grule T (UnionNT g₁.nt g₂.nt) where
  input_L := []
  input_N := UnionNT.start
  input_R := []
  output_string := [symbol.nonterminal (UnionNT.left g₁.initial)]

private def unionStartRight (g₁ g₂ : grammar T) :
    grule T (UnionNT g₁.nt g₂.nt) where
  input_L := []
  input_N := UnionNT.start
  input_R := []
  output_string := [symbol.nonterminal (UnionNT.right g₂.initial)]

private def ncUnionGrammar (g₁ g₂ : grammar T) : grammar T where
  nt := UnionNT g₁.nt g₂.nt
  initial := UnionNT.start
  rules :=
    unionStartLeft g₁ g₂ ::
    unionStartRight g₁ g₂ ::
    (g₁.rules.map (lift_rule_ (UnionNT.left : g₁.nt → UnionNT g₁.nt g₂.nt)) ++
      g₂.rules.map (lift_rule_ (UnionNT.right : g₂.nt → UnionNT g₁.nt g₂.nt)))

private def sinkLeft (g₁ g₂ : grammar T) : UnionNT g₁.nt g₂.nt → Option g₁.nt
  | UnionNT.left n => some n
  | _ => none

private def sinkRight (g₁ g₂ : grammar T) : UnionNT g₁.nt g₂.nt → Option g₂.nt
  | UnionNT.right n => some n
  | _ => none

private def lgLeft (g₁ g₂ : grammar T) : lifted_grammar_ T where
  g₀ := g₁
  g := ncUnionGrammar g₁ g₂
  lift_nt := UnionNT.left
  sink_nt := sinkLeft g₁ g₂
  lift_inj := by
    intro a b h
    injection h
  sink_inj := by
    intro x y h
    cases x with
    | start =>
        exact Or.inr rfl
    | left a =>
        cases y with
        | start => simp [sinkLeft] at h
        | left b =>
            left
            simp [sinkLeft] at h
            rw [h]
        | right b => simp [sinkLeft] at h
    | right a =>
        exact Or.inr rfl
  lift_nt_sink := by
    intro n
    rfl
  corresponding_rules := by
    intro r hr
    simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))
  preimage_of_rules := by
    intro r hr
    rcases hr with ⟨hr, n, hn⟩
    simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map] at hr
    rcases hr with rfl | rfl | hleft | hright
    · simp [unionStartLeft] at hn
    · simp [unionStartRight] at hn
    · rcases hleft with ⟨r₀, hr₀, rfl⟩
      exact ⟨r₀, hr₀, rfl⟩
    · rcases hright with ⟨r₀, _hr₀, rfl⟩
      simp [lift_rule_] at hn

private def lgRight (g₁ g₂ : grammar T) : lifted_grammar_ T where
  g₀ := g₂
  g := ncUnionGrammar g₁ g₂
  lift_nt := UnionNT.right
  sink_nt := sinkRight g₁ g₂
  lift_inj := by
    intro a b h
    injection h
  sink_inj := by
    intro x y h
    cases x with
    | start =>
        exact Or.inr rfl
    | left a =>
        exact Or.inr rfl
    | right a =>
        cases y with
        | start => simp [sinkRight] at h
        | left b => simp [sinkRight] at h
        | right b =>
            left
            simp [sinkRight] at h
            rw [h]
  lift_nt_sink := by
    intro n
    rfl
  corresponding_rules := by
    intro r hr
    simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))
  preimage_of_rules := by
    intro r hr
    rcases hr with ⟨hr, n, hn⟩
    simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map] at hr
    rcases hr with rfl | rfl | hleft | hright
    · simp [unionStartLeft] at hn
    · simp [unionStartRight] at hn
    · rcases hleft with ⟨r₀, _hr₀, rfl⟩
      simp [lift_rule_] at hn
    · rcases hright with ⟨r₀, hr₀, rfl⟩
      exact ⟨r₀, hr₀, rfl⟩

private theorem ncUnion_noncontracting (g₁ g₂ : grammar T)
    (h₁ : grammar_noncontracting g₁) (h₂ : grammar_noncontracting g₂) :
    grammar_noncontracting (ncUnionGrammar g₁ g₂) := by
  intro r hr
  simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | rfl | hleft | hright
  · simp [unionStartLeft]
  · simp [unionStartRight]
  · rcases hleft with ⟨r₁, hr₁, rfl⟩
    simpa [grammar_noncontracting, lift_rule_, lift_string_] using h₁ r₁ hr₁
  · rcases hright with ⟨r₂, hr₂, rfl⟩
    simpa [grammar_noncontracting, lift_rule_, lift_string_] using h₂ r₂ hr₂

private lemma ncUnion_first_step {g₁ g₂ : grammar T}
    {β : List (symbol T (ncUnionGrammar g₁ g₂).nt)}
    (h : grammar_transforms (ncUnionGrammar g₁ g₂)
      [symbol.nonterminal (ncUnionGrammar g₁ g₂).initial] β) :
    β = [symbol.nonterminal (UnionNT.left g₁.initial)] ∨
      β = [symbol.nonterminal (UnionNT.right g₂.initial)] := by
  obtain ⟨r, hr, u, v, hbef, haft⟩ := h
  have huv : u = [] ∧ v = [] := by
    have hlen := congrArg List.length hbef
    simp only [ncUnionGrammar, List.length_cons, List.length_nil, List.length_append] at hlen
    constructor <;> (rw [← List.length_eq_zero_iff]; omega)
  have hLR : r.input_L = [] ∧ r.input_R = [] := by
    have hlen := congrArg List.length hbef
    rw [huv.1, huv.2] at hlen
    simp only [ncUnionGrammar, List.nil_append, List.append_nil, List.length_cons,
      List.length_nil, List.length_append] at hlen
    constructor <;> (rw [← List.length_eq_zero_iff]; omega)
  rw [huv.1, huv.2] at hbef haft
  rw [hLR.1, hLR.2] at hbef
  simp only [List.nil_append, List.append_nil] at hbef haft
  have hN : r.input_N = UnionNT.start := by
    have hsym : (symbol.nonterminal r.input_N :
        symbol T (UnionNT g₁.nt g₂.nt)) = symbol.nonterminal UnionNT.start := by
      simpa [ncUnionGrammar] using hbef.symm
    exact symbol.nonterminal.inj hsym
  simp only [ncUnionGrammar, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | rfl | hleft | hright
  · left
    simpa [unionStartLeft] using haft
  · right
    simpa [unionStartRight] using haft
  · rcases hleft with ⟨r₁, _hr₁, rfl⟩
    simp [lift_rule_] at hN
  · rcases hright with ⟨r₂, _hr₂, rfl⟩
    simp [lift_rule_] at hN

private theorem ncUnion_language (g₁ g₂ : grammar T) :
    grammar_language (ncUnionGrammar g₁ g₂) = grammar_language g₁ + grammar_language g₂ := by
  ext w
  constructor
  · intro hw
    change grammar_generates (ncUnionGrammar g₁ g₂) w at hw
    unfold grammar_generates at hw
    rcases grammar_tran_or_id_of_deri hw with hbad | ⟨β, hfirst, hrest⟩
    · have hmem : symbol.nonterminal (UnionNT.start : UnionNT g₁.nt g₂.nt) ∈
          w.map (symbol.terminal (N := UnionNT g₁.nt g₂.nt)) := by
        rw [← hbad]
        simp [ncUnionGrammar]
      rw [List.mem_map] at hmem
      obtain ⟨a, _ha, hterm⟩ := hmem
      cases hterm
    · rcases ncUnion_first_step hfirst with hβ | hβ
      · left
        change grammar_generates g₁ w
        unfold grammar_generates
        rw [hβ] at hrest
        have hsink := sink_deri_ (lgLeft g₁ g₂) hrest (by
          intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          exact ⟨g₁.initial, rfl⟩)
        simpa [lgLeft, sink_string_, sink_symbol_, sinkLeft, Function.comp_def] using hsink
      · right
        change grammar_generates g₂ w
        unfold grammar_generates
        rw [hβ] at hrest
        have hsink := sink_deri_ (lgRight g₁ g₂) hrest (by
          intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          exact ⟨g₂.initial, rfl⟩)
        simpa [lgRight, sink_string_, sink_symbol_, sinkRight, Function.comp_def] using hsink
  · intro hw
    rcases hw with hw | hw
    · change grammar_generates (ncUnionGrammar g₁ g₂) w
      change grammar_generates g₁ w at hw
      unfold grammar_generates at hw ⊢
      refine grammar_deri_of_tran_deri (g := ncUnionGrammar g₁ g₂)
        (v := [symbol.nonterminal (UnionNT.left g₁.initial)]) ?_ ?_
      · exact ⟨unionStartLeft g₁ g₂, by simp [ncUnionGrammar], [], [], by simp [ncUnionGrammar, unionStartLeft],
          by simp [unionStartLeft]⟩
      · have hlift := lift_deri_ (lgLeft g₁ g₂) hw
        simpa [lift_string_, lift_symbol_, ncUnionGrammar] using hlift
    · change grammar_generates (ncUnionGrammar g₁ g₂) w
      change grammar_generates g₂ w at hw
      unfold grammar_generates at hw ⊢
      refine grammar_deri_of_tran_deri (g := ncUnionGrammar g₁ g₂)
        (v := [symbol.nonterminal (UnionNT.right g₂.initial)]) ?_ ?_
      · exact ⟨unionStartRight g₁ g₂, by simp [ncUnionGrammar], [], [], by simp [ncUnionGrammar, unionStartRight],
          by simp [unionStartRight]⟩
      · have hlift := lift_deri_ (lgRight g₁ g₂) hw
        simpa [lift_string_, lift_symbol_, ncUnionGrammar] using hlift

private lemma diff_singleton_eq_of_not_mem {L : Language T} (hε : [] ∉ L) :
    L \ ({[]} : Set (List T)) = L := by
  ext w
  constructor
  · intro hw
    exact hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    intro hnil
    rw [Set.mem_singleton_iff] at hnil
    exact hε (by simpa [hnil] using hw)

private lemma empty_or_diff_singleton_eq_of_mem {L : Language T} (hε : [] ∈ L) :
    (fun w : List T => w = [] ∨ w ∈ L \ ({[]} : Set (List T))) = L := by
  ext w
  constructor
  · rintro (rfl | hw)
    · exact hε
    · exact hw.1
  · intro hw
    by_cases hnil : w = []
    · exact Or.inl hnil
    · exact Or.inr ⟨hw, by simpa [Set.mem_singleton_iff] using hnil⟩

private lemma union_diff_singleton (L₁ L₂ : Language T) :
    (L₁ \ ({[]} : Set (List T))) + (L₂ \ ({[]} : Set (List T))) =
      (L₁ + L₂) \ ({[]} : Set (List T)) := by
  ext w
  constructor
  · rintro (hw | hw)
    · exact ⟨Or.inl hw.1, hw.2⟩
    · exact ⟨Or.inr hw.1, hw.2⟩
  · rintro ⟨hw, hwne⟩
    rcases hw with hw | hw
    · exact Or.inl ⟨hw, hwne⟩
    · exact Or.inr ⟨hw, hwne⟩

end ContextSensitiveUnion

open ContextSensitiveUnion

/-- Context-sensitive languages are closed under union. -/
public theorem CS_closedUnderUnion : ClosedUnderUnion (α := T) is_CS := by
  intro L₁ L₂ hL₁ hL₂
  obtain ⟨g₁, hg₁, hlang₁⟩ := hL₁
  obtain ⟨g₂, hg₂, hlang₂⟩ := hL₂
  obtain ⟨g₁', _hfin₁, hnc₁, hlang₁'⟩ := exists_noncontracting_offEmpty_of_CS g₁ hg₁
  obtain ⟨g₂', _hfin₂, hnc₂, hlang₂'⟩ := exists_noncontracting_offEmpty_of_CS g₂ hg₂
  let G := ncUnionGrammar g₁' g₂'
  have hGnc : grammar_noncontracting G := ncUnion_noncontracting g₁' g₂' hnc₁ hnc₂
  have hG :
      grammar_language G = (L₁ + L₂) \ ({[]} : Set (List T)) := by
    dsimp [G]
    rw [ncUnion_language, hlang₁', hlang₂', hlang₁, hlang₂, union_diff_singleton]
  by_cases hε : ([] : List T) ∈ L₁ + L₂
  · have hAdd := is_CS_insert_empty_of_noncontracting G hGnc
    convert hAdd using 1
    rw [hG]
    exact (empty_or_diff_singleton_eq_of_mem hε).symm
  · have hNoEmpty : grammar_language G = L₁ + L₂ := by
      rw [hG, diff_singleton_eq_of_not_mem hε]
    exact ⟨G, grammar_context_sensitive_of_noncontracting G hGnc, hNoEmpty⟩
