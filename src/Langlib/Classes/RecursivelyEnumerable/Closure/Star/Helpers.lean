module

public import Langlib.Grammars.Unrestricted.Definition
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Utilities.ListUtils
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Helper lemmas for RE closure under Kleene star -/

variable {T : Type}

namespace StarHelpers

section star_helpers

@[expose]
public abbrev nn (N : Type) : Type := N ⊕ Fin 3
@[expose]
public abbrev ns (T N : Type) : Type := symbol T (nn N)

@[expose]
public def Z {N : Type} : ns T N := symbol.nonterminal (Sum.inr 0)
@[expose]
public def H {N : Type} : ns T N := symbol.nonterminal (Sum.inr 1)
@[expose]
public def R {N : Type} : ns T N := symbol.nonterminal (Sum.inr 2)

@[expose]
public def wrap_sym {N : Type} : symbol T N → ns T N
  | symbol.terminal t    => symbol.terminal t
  | symbol.nonterminal n => symbol.nonterminal (Sum.inl n)

public lemma wrap_sym_injective {N : Type} : Function.Injective (@wrap_sym T N) := by
  intro a b h; cases a <;> cases b <;> simp [wrap_sym] at h <;> exact congrArg _ h

/-- `symbol.nonterminal (Sum.inr i)` does not appear in `List.map wrap_sym l`. -/
public lemma inr_not_in_map_wrap {N : Type} {l : List (symbol T N)} {i : Fin 3} :
    symbol.nonterminal (Sum.inr i) ∉ List.map (@wrap_sym T N) l := by
  intro h; rw [List.mem_map] at h
  rcases h with ⟨a, _, ha⟩
  cases a <;> simp [wrap_sym] at ha

/-- No `Sum.inr i` nonterminal (other than H) appears in the flattened block structure. -/
public lemma inr_not_in_blocks {N : Type} {x : List (List (symbol T N))} {i : Fin 3}
    (hi : symbol.nonterminal (Sum.inr i) ≠ @H T N) :
    symbol.nonterminal (Sum.inr i) ∉
      (List.map (· ++ [H]) (List.map (List.map (@wrap_sym T N)) x)).flatten := by
  intro h
  rw [List.mem_flatten] at h
  rcases h with ⟨l, hl_mem, h_in_l⟩
  rw [List.mem_map] at hl_mem
  rcases hl_mem with ⟨l', hl'_mem, rfl⟩
  rw [List.mem_map] at hl'_mem
  rcases hl'_mem with ⟨block, _, rfl⟩
  rw [List.mem_append] at h_in_l
  rcases h_in_l with h_in_wrap | h_in_H
  · exact inr_not_in_map_wrap h_in_wrap
  · rw [List.mem_singleton] at h_in_H
    exact hi h_in_H

public lemma Z_not_in_blocks {N : Type} {x : List (List (symbol T N))} :
    @Z T N ∉ (List.map (· ++ [H]) (List.map (List.map wrap_sym) x)).flatten :=
  inr_not_in_blocks (by simp [H])

public lemma R_not_in_blocks {N : Type} {x : List (List (symbol T N))} :
    @R T N ∉ (List.map (· ++ [H]) (List.map (List.map wrap_sym) x)).flatten :=
  inr_not_in_blocks (by simp [H])

/-
H does not appear in the input pattern of a wrapped rule.
-/
public lemma H_not_in_wrapped_input {N : Type} {r₀ : grule T N} :
    @H T N ∉ List.map wrap_sym r₀.input_L ++
      [symbol.nonterminal (Sum.inl r₀.input_N)] ++
      List.map wrap_sym r₀.input_R := by
  simp +decide [ H ];
  constructor <;> intro x hx <;> intro H <;> cases x <;> cases H


/-
Key decomposition: if a wrapped rule pattern matches in the flattened block structure,
    then the match occurs entirely within one block.
-/
public lemma match_in_block {N : Type} {r₀ : grule T N}
    {x : List (List (symbol T N))} {u v : List (ns T N)} (xne : x ≠ [])
    (hyp : (List.map (· ++ [@H T N]) (List.map (List.map wrap_sym) x)).flatten =
      u ++ List.map wrap_sym r₀.input_L ++
        [symbol.nonterminal (Sum.inl r₀.input_N)] ++
        List.map wrap_sym r₀.input_R ++ v) :
  ∃ (x₁ : List (List (symbol T N))) (xₘ : List (symbol T N)) (x₂ : List (List (symbol T N)))
    (u₁ v₁ : List (symbol T N)),
    x = x₁ ++ [xₘ] ++ x₂ ∧
    xₘ = u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁ ∧
    u = (List.map (· ++ [H]) (List.map (List.map wrap_sym) x₁)).flatten ++
        List.map wrap_sym u₁ ∧
    v = List.map wrap_sym v₁ ++ [H] ++
        (List.map (· ++ [H]) (List.map (List.map wrap_sym) x₂)).flatten := by
  induction' x with x₁ x ih generalizing u v <;> simp +decide [ * ] at *;
  -- Apply the split_at_separator lemma with the separator being H and the middle part being the rule pattern.
  have h_split : ∃ u' : List (ns T N), List.map wrap_sym x₁ = u ++ (List.map wrap_sym r₀.input_L ++ symbol.nonterminal (Sum.inl r₀.input_N) :: (List.map wrap_sym r₀.input_R ++ u')) ∨ ∃ v' : List (ns T N), u = List.map wrap_sym x₁ ++ H :: v' ∧ (List.map ((fun x => x ++ [H]) ∘ List.map wrap_sym) x).flatten = v' ++ (List.map wrap_sym r₀.input_L ++ symbol.nonterminal (Sum.inl r₀.input_N) :: (List.map wrap_sym r₀.input_R ++ v)) := by
    have h_split : ∀ {a b u mid v : List (ns T N)} {sep : ns T N}, sep ∉ mid → a ++ [sep] ++ b = u ++ mid ++ v → (∃ u' : List (ns T N), a = u ++ mid ++ u' ∧ v = u' ++ [sep] ++ b) ∨ (∃ v' : List (ns T N), u = a ++ [sep] ++ v' ∧ b = v' ++ mid ++ v) := by
      exact?
    generalize_proofs at *; (
    specialize @h_split ( List.map wrap_sym x₁ ) ( List.map ( ( fun x => x ++ [ H ] ) ∘ List.map wrap_sym ) x |> List.flatten ) u ( List.map wrap_sym r₀.input_L ++ symbol.nonterminal ( Sum.inl r₀.input_N ) :: List.map wrap_sym r₀.input_R ) v H ; simp_all +decide [  ] ;
    contrapose! h_split; simp_all +decide [ wrap_sym ] ;
    refine' ⟨ _, _, _, _ ⟩;
    · intro x hx; cases x <;> simp +decide [ H ] ;
    · exact ne_of_apply_ne ( fun x => x ) ( by simp +decide [ H ] );
    · rintro ( _ | _ ) <;> simp +decide [ H ];
    · exact fun v' hv' => h_split v' |>.2 v' hv');
  rcases h_split with ⟨ u', hu' | ⟨ v', rfl, hv ⟩ ⟩;
  · -- Since `wrap_sym` is injective, we can split the equality into two parts: `u` and `u'`.
    obtain ⟨u₁, hu₁⟩ : ∃ u₁ : List (symbol T N), u = List.map wrap_sym u₁ := by
      have h_split : u = List.take (List.length u) (List.map wrap_sym x₁) := by
        rw [ hu', List.take_append_of_le_length ] <;> norm_num;
      use List.take (List.length u) x₁;
      rw [ h_split, List.map_take ];
      grind +qlia
    obtain ⟨v₁, hv₁⟩ : ∃ v₁ : List (symbol T N), u' = List.map wrap_sym v₁ := by
      have h_inj : ∀ {l : List (ns T N)}, (∀ s ∈ l, ∃ s' : symbol T N, wrap_sym s' = s) → ∃ l' : List (symbol T N), l = List.map wrap_sym l' := by
        intros l hl; induction' l with s l ih <;> simp_all +decide [  ] ;
        rcases hl.1 with ⟨ s', rfl ⟩ ; rcases ih with ⟨ l', rfl ⟩ ; exact ⟨ s' :: l', by simp +decide ⟩ ;
      apply h_inj;
      intro s hs; replace hu' := congr_arg ( fun l => s ∈ l ) hu'; simp_all +decide [ List.mem_append, List.mem_map ] ;
      exact hu'.imp fun x hx => hx.2;
    use [], x, u₁, v₁; simp_all +decide [  ] ;
    exact List.map_injective_iff.mpr ( wrap_sym_injective ) <| by simpa using hu';
  · by_cases hx : x = [] <;> simp_all +decide [  ];
    grind

/-
After applying a wrapped rule within a block, the result has the same block structure
    with the affected block updated.
-/
public lemma update_block_in_flatten {N : Type}
    {x₁ : List (List (symbol T N))} {x₂ : List (List (symbol T N))}
    {u₁ v₁ : List (symbol T N)}
    {r₀ : grule T N} :
  (List.map (· ++ [@H T N]) (List.map (List.map wrap_sym) x₁)).flatten ++
    List.map wrap_sym u₁ ++ List.map wrap_sym r₀.output_string ++
    List.map wrap_sym v₁ ++ [H] ++
    (List.map (· ++ [H]) (List.map (List.map wrap_sym) x₂)).flatten =
  (List.map (· ++ [H]) (List.map (List.map wrap_sym)
    (x₁ ++ [u₁ ++ r₀.output_string ++ v₁] ++ x₂))).flatten := by
  grind

/-
Validity is preserved when updating a block.
-/
public lemma valid_update_block
    {g : grammar T}
    {x₁ : List (List (symbol T g.nt))} {x₂ : List (List (symbol T g.nt))}
    {u₁ v₁ : List (symbol T g.nt)}
    {r₀ : grule T g.nt}
    (hvalid : ∀ xᵢ ∈ x₁ ++ [u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++
        r₀.input_R ++ v₁] ++ x₂,
      grammar_derives g [symbol.nonterminal g.initial] xᵢ)
    (hr₀ : r₀ ∈ g.rules) :
  ∀ xᵢ ∈ x₁ ++ [u₁ ++ r₀.output_string ++ v₁] ++ x₂,
    grammar_derives g [symbol.nonterminal g.initial] xᵢ := by
  have h_transform : grammar_transforms g (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁) (u₁ ++ r₀.output_string ++ v₁) := by
    constructor;
    exact ⟨ hr₀, u₁, v₁, rfl, rfl ⟩;
  have h_derive : grammar_derives g [symbol.nonterminal g.initial] (u₁ ++ r₀.output_string ++ v₁) := by
    exact grammar_deri_of_deri_tran ( hvalid _ <| by aesop ) h_transform;
  aesop


/-
R only appears at position 0 in [R, H] ++ blocks.
-/
public lemma R_only_at_head {N : Type} {x : List (List (symbol T N))} :
    @R T N ∉ (@H T N :: (List.map (· ++ [H]) (List.map (List.map wrap_sym) x)).flatten) := by
  simp [R, H];
  unfold wrap_sym; aesop;

end star_helpers

end StarHelpers
