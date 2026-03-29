/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.Pushdown.Basics.DPDA
import Grammars.Classes.ContextFree.Basics.PDAEquivalence
import Grammars.Classes.ContextFree.ClosureProperties.Complement
import Grammars.Classes.ContextFree.ClosureProperties.Intersection

/-! # Deterministic Context-Free Languages (DCFLs)

This file defines the class of deterministic context-free languages (DCFLs) and
establishes two fundamental results:

1. **DCFLs are closed under complementation** (`is_DCFL_compl`).
2. **There exist CFLs that are not DCFLs** (`exists_CF_not_DCFL`), i.e., DCFL ⊊ CFL.

## Definition

A language `L` is a **deterministic context-free language (DCFL)** if there exists a
deterministic pushdown automaton (DPDA) that accepts `L` by final-state acceptance.

## Main results

- `is_CF_of_is_DCFL` — Every DCFL is context-free.
- `is_DCFL_compl` — The class of DCFLs is closed under complementation.
- `complement_CF_of_all_CF_DCFL` — If all CFLs are DCFLs, then CFLs are closed under complement.
- `exists_CF_not_DCFL` — There exist CFLs that are not DCFLs, i.e., DCFL ⊊ CFL.
- `lang_aibjck_eq_union` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` equals the union of two CFLs.
- `lang_aibjck_CFL` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` is context-free.
- `not_DCFL_lang_aibjck` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` is not a DCFL.

## Proof sketch for DCFL complement closure

Given a DPDA `M` accepting a language `L` by final-state acceptance, one constructs a
new DPDA `M'` accepting `Lᶜ`. The construction involves:

1. **Making `M` loop-free**: Modify `M` so that it never enters an infinite sequence
   of ε-transitions. This is achieved by bounding the number of consecutive ε-steps.

2. **Making `M` total**: Ensure that `M` always has a transition available (until the
   stack is empty), by adding a "dead" non-accepting sink state.

3. **Ensuring `M` reads all input**: The modifications above guarantee that for every
   input word `w`, the computation on `w` terminates after reading all of `w`.

4. **Handling the ε-transition acceptance subtlety**: After reading the last input symbol,
   `M` may perform ε-transitions that pass through both accepting and non-accepting states.
   The complement machine `M'` tracks, via an auxiliary component in its state space,
   whether an accepting state has been visited since the last input symbol was read.

5. **Swapping acceptance**: The accepting states of `M'` are chosen so that `M'` accepts
   precisely when `M` does not.

This construction is due to Hopcroft and Ullman (1979).

## Proof sketch for CFL ⊄ DCFL

The proof uses the closure of DCFLs under complementation together with the classical
result that CFLs are *not* closed under complementation (`nnyCF_of_complement_CF`).

If every CFL were a DCFL, then every CFL's complement would be a DCFL (by DCFL complement
closure), hence a CFL (since every DCFL is a CFL). But this would mean CFLs are closed
under complementation, contradicting `nnyCF_of_complement_CF`. Therefore, there exist
CFLs that are not DCFLs.

The standard explicit witness is the language `{aⁱ bʲ cᵏ | i = j ∨ j = k}` over the
three-letter alphabet `{a, b, c}`. This language is context-free (as the union of the
CFLs `{aⁿ bⁿ cᵐ}` and `{aⁿ bᵐ cᵐ}`), but not deterministic context-free, because
its complement intersected with the regular language `a*b*c*` yields
`{aⁱ bʲ cᵏ | i ≠ j ∧ j ≠ k}`, which is not context-free (provable by Ogden's lemma).

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Theorem 6.15 (complementation) and Theorem 6.16 (CFL ⊄ DCFL).
-/

open PDA

variable {T : Type} [Fintype T]

-- ============================================================================
-- DCFL definition and basic properties
-- ============================================================================

/-- A language `L` over a finite alphabet `T` is a **deterministic context-free language
    (DCFL)** if there exists a DPDA that recognizes `L` via final-state acceptance. -/
def is_DCFL (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S) (M : DPDA Q T S),
    M.acceptsByFinalState = L

-- ============================================================================
-- PDA Final-State → PDA Empty-Stack conversion
-- ============================================================================

section PDA_FS_to_ES

open Classical in
/-- ε-transition function for the FS→ES PDA conversion.
    Defined as a top-level function to ensure good definitional reduction. -/
noncomputable def PDA_FS_to_ES_eps {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inr 0, none => {(Sum.inl M.initial_state, [some M.start_symbol, none])}
  | Sum.inl q, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun' q s)
        ∪ (if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅)
  | Sum.inl q, none =>
      if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅
  | Sum.inr 1, _ => {(Sum.inr 1, [])}
  | Sum.inr 0, some _ => ∅

open Classical in
/-- Input-reading transition function for the FS→ES PDA conversion. -/
noncomputable def PDA_FS_to_ES_trans {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → T → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inl q, a, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun q a s)
  | _, _, _ => ∅

open Classical in
/-- The PDA that converts final-state acceptance to empty-stack acceptance. -/
noncomputable def PDA_FS_to_ES_pda {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : PDA (Q ⊕ Fin 2) T (Option S) where
  initial_state := Sum.inr 0
  start_symbol := none
  final_states := ∅
  transition_fun := PDA_FS_to_ES_trans M
  transition_fun' := PDA_FS_to_ES_eps M
  finite q' a Z' := by
    simp only [PDA_FS_to_ES_trans]
    split <;> try exact Set.toFinite _
    exact (M.finite _ a _).image _
  finite' q' Z' := by
    simp only [PDA_FS_to_ES_eps]
    split <;> try exact Set.toFinite _
    · exact ((M.finite' _ _).image _).union (by split_ifs <;> exact Set.toFinite _)
    · exact (by split_ifs <;> exact Set.toFinite _)

/-- Lifting a configuration from the original PDA to the new PDA. -/
def liftConf {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) (c : PDA.conf M) : PDA.conf (PDA_FS_to_ES_pda M) :=
  ⟨Sum.inl c.state, c.input, c.stack.map some ++ [none]⟩

/-
PROBLEM
One-step simulation: if M takes one step from r₁ to r₂, then M' can
    take one step from lift(r₁) to lift(r₂).

PROVIDED SOLUTION
We need to show that if M takes one step from r₁ to r₂, then PDA_FS_to_ES_pda M takes one step from liftConf M r₁ to liftConf M r₂.

PDA.Reaches₁ r₁ r₂ means r₂ ∈ PDA.step r₁. By the definition of step:
- If r₁ = (q, a::w, Z::α): r₂ = (p, w, β++α) for some (p,β) ∈ M.transition_fun q a Z, OR r₂ = (p, a::w, β++α) for (p,β) ∈ M.transition_fun' q Z
- If r₁ = (q, [], Z::α): r₂ = (p, [], β++α) for (p,β) ∈ M.transition_fun' q Z
- If r₁ = (_, _, []): impossible (step returns ∅)

For liftConf: liftConf M ⟨q, w, γ⟩ = ⟨Sum.inl q, w, γ.map some ++ [none]⟩

Case 1: r₁ = ⟨q, a::w, Z::α⟩, r₂ = ⟨p, w, β++α⟩ with (p,β) ∈ M.transition_fun q a Z
- liftConf r₁ = ⟨Sum.inl q, a::w, (some Z)::(α.map some ++ [none])⟩
- liftConf r₂ = ⟨Sum.inl p, w, (β.map some)++(α.map some ++ [none])⟩
  = ⟨Sum.inl p, w, β.map some ++ α.map some ++ [none]⟩
- In M', step from liftConf r₁: PDA_FS_to_ES_trans M (Sum.inl q) a (some Z) contains (Sum.inl p, β.map some)
  because (p, β) ∈ M.transition_fun q a Z, so (Sum.inl p, β.map some) is in the image.
  The new config is ⟨Sum.inl p, w, β.map some ++ (α.map some ++ [none])⟩ = liftConf r₂. ✓

Case 2: r₁ = ⟨q, a::w, Z::α⟩ (or ⟨q, [], Z::α⟩), r₂ = ⟨p, input, β++α⟩ with (p,β) ∈ M.transition_fun' q Z
- Similar: PDA_FS_to_ES_eps M (Sum.inl q) (some Z) contains (Sum.inl p, β.map some) from the image part.
- Need to use List.map_append to show β.map some ++ α.map some ++ [none] = (β ++ α).map some ++ [none]

The key list identity needed is: (β ++ α).map some ++ [none] = β.map some ++ (α.map some ++ [none]), which follows from List.map_append and List.append_assoc.
-/
lemma simulation_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches₁ r₁ r₂) :
    PDA.Reaches₁ (liftConf M r₁) (liftConf M r₂) := by
  cases r₁ ; cases r₂ ; simp_all +decide [ Reaches₁ ];
  unfold step at *;
  rename_i q w α q' w' α';
  rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases α with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ liftConf ];
  · rcases h with ⟨ β, hβ, rfl, rfl ⟩ ; use β.map some; simp_all +decide [ PDA_FS_to_ES_pda ] ;
    unfold PDA_FS_to_ES_eps; aesop;
  · rcases h with ( ⟨ β, hβ, rfl, rfl ⟩ | ⟨ β, hβ, rfl, rfl ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda ];
    · exact Set.mem_image_of_mem _ hβ;
    · exact Set.mem_union_left _ ( Set.mem_image_of_mem _ hβ )

/-- Multi-step simulation: if M reaches r₂ from r₁, then M' reaches
    lift(r₂) from lift(r₁). -/
lemma simulation_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches r₁ r₂) :
    PDA.Reaches (liftConf M r₁) (liftConf M r₂) := by
  induction h with
  | refl => rfl
  | tail _ h₂ ih => exact Relation.ReflTransGen.tail ih (simulation_step M _ _ h₂)

/-
PROBLEM
The drain state can reach empty stack from any stack configuration.

PROVIDED SOLUTION
By induction on γ.

Base case: γ = []. Then we need Reaches ⟨inr 1, [], []⟩ ⟨inr 1, [], []⟩, which is Reaches.refl.

Inductive case: γ = Z :: γ'. We have stack [Z, ...γ'].
In PDA_FS_to_ES_pda M, from state (Sum.inr 1) with stack top Z (any Option S value):
PDA_FS_to_ES_eps M (Sum.inr 1) Z = {(Sum.inr 1, [])}.
So there's an ε-transition that pops Z and stays in state inr 1.
After this step: ⟨Sum.inr 1, [], γ'⟩.
By the induction hypothesis, Reaches ⟨Sum.inr 1, [], γ'⟩ ⟨Sum.inr 1, [], []⟩.
Chain: Reaches₁ then Reaches gives the result.

The step proof: from ⟨Sum.inr 1, [], Z :: γ'⟩, PDA.step looks at the case ⟨q, [], Z::α⟩ and returns {r₂ | ∃ p β, (p,β) ∈ transition_fun' (inr 1) Z ∧ r₂ = ⟨p, [], β ++ γ'⟩}.
Since PDA_FS_to_ES_eps M (Sum.inr 1) Z = {(Sum.inr 1, [])}, we have (Sum.inr 1, []) ∈ this set.
So r₂ = ⟨Sum.inr 1, [], [] ++ γ'⟩ = ⟨Sum.inr 1, [], γ'⟩ is reachable in one step.
-/
lemma drain_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (γ : List (Option S)) :
    @PDA.Reaches (Q ⊕ Fin 2) T (Option S) _ _ _ (PDA_FS_to_ES_pda M)
      ⟨Sum.inr 1, [], γ⟩ ⟨Sum.inr 1, [], []⟩ := by
  induction' γ with Z γ ih generalizing M;
  · constructor;
  · -- From ⟨Sum.inr 1, [], [Z, γ]⟩, we can transition to ⟨Sum.inr 1, [], γ⟩ using the ε-transition.
    have h_step : Reaches₁ (⟨Sum.inr 1, [], Z :: γ⟩ : PDA.conf (PDA_FS_to_ES_pda M)) (⟨Sum.inr 1, [], γ⟩ : PDA.conf (PDA_FS_to_ES_pda M)) := by
      unfold PDA.Reaches₁;
      unfold step; aesop;
    exact .single h_step |> Relation.ReflTransGen.trans <| ih M

/-
PROBLEM
Forward direction of PDA_FS_subset_ES.

PROVIDED SOLUTION
Given w ∈ M.acceptsByFinalState, there exist q ∈ M.final_states and γ such that M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩.

We need to show w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack, i.e., there exists q' such that (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inr 0, w, [none]⟩ ⟨q', [], []⟩.

Construction of the path in M':

Step 1: ε-transition from ⟨Sum.inr 0, w, [none]⟩ to ⟨Sum.inl M.initial_state, w, [some M.start_symbol, none]⟩.
This uses PDA_FS_to_ES_eps M (Sum.inr 0) none = {(Sum.inl M.initial_state, [some M.start_symbol, none])}.
The step is: PDA.step ⟨Sum.inr 0, w, [none]⟩ contains ⟨Sum.inl M.initial_state, w, [some M.start_symbol, none]⟩.
For w = []: step ⟨q, [], Z::α⟩ = {r | ∃ p β, (p,β) ∈ transition_fun' q Z ∧ r = ⟨p, [], β++α⟩}.
For w = a::w': step gives union of input-reading and ε-transitions on Z::α.
In both cases, the ε-transition is available.

Step 2: By simulation_reaches, since M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩, we have (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inl M.initial_state, w, [some M.start_symbol, none]⟩ ⟨Sum.inl q, [], γ.map some ++ [none]⟩.
This uses liftConf M ⟨M.initial_state, w, [M.start_symbol]⟩ = ⟨Sum.inl M.initial_state, w, [some M.start_symbol, none]⟩ and similarly for the target.

Step 3: Since q ∈ M.final_states, from ⟨Sum.inl q, [], γ.map some ++ [none]⟩:
- If γ is non-empty, say γ = Z :: γ': the top of stack is some Z. PDA_FS_to_ES_eps M (Sum.inl q) (some Z) contains (Sum.inr 1, []) (since q ∈ F). So Reaches₁ to ⟨Sum.inr 1, [], γ'.map some ++ [none]⟩.
- If γ is empty: the top of stack is none. PDA_FS_to_ES_eps M (Sum.inl q) none = {(Sum.inr 1, [])} (since q ∈ F). So Reaches₁ to ⟨Sum.inr 1, [], []⟩.

Step 4: By drain_reaches, from ⟨Sum.inr 1, [], remaining_stack⟩ to ⟨Sum.inr 1, [], []⟩.

Chain all these transitions to get the result. Take q' = Sum.inr 1.
-/
lemma PDA_FS_to_ES_forward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ M.acceptsByFinalState) :
    w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
  -- By definition of $PDA_FS_to_ES_pda$, we know that if $w \in M.acceptsByFinalState$, then there exists a path in $PDA_FS_to_ES_pda$ leading to an empty stack.
  have h_path : ∀ (q : Q) (γ : List S) (hq : q ∈ M.final_states) (hγ : M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩), w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
    intro q γ hq hγ
    have h_lift : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inr 0, w, [none]⟩ ⟨Sum.inl q, [], γ.map some ++ [none]⟩ := by
      convert PDA.Reaches.trans _ ( simulation_reaches M _ _ hγ ) using 1;
      constructor ; aesop;
      -- By definition of `Reaches₁`, we can use the ε-transition to move from `Sum.inr 0` to `Sum.inl M.initial_state`.
      apply Set.mem_setOf_eq.mpr;
      cases w <;> simp +decide [ liftConf ];
      · exact Or.inl ⟨ _, _, by tauto, rfl ⟩;
      · exact Or.inr <| Or.inl <| by unfold PDA_FS_to_ES_pda; aesop;
    -- By definition of $PDA_FS_to_ES_pda$, we know that if $q \in M.final_states$, then there exists a path in $PDA_FS_to_ES_pda$ leading to an empty stack.
    have h_path : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inl q, [], γ.map some ++ [none]⟩ ⟨Sum.inr 1, [], []⟩ := by
      induction' γ with Z γ ih generalizing q <;> simp_all +decide [ Reaches ];
      · apply_rules [ Relation.ReflTransGen.single ];
        -- By definition of $PDA_FS_to_ES_pda$, we know that if $q \in M.final_states$, then there exists a path in $PDA_FS_to_ES_pda$ leading to an empty stack. Use this fact.
        simp [Reaches₁, PDA_FS_to_ES_pda];
        simp +decide [ step, hq ];
        unfold PDA_FS_to_ES_eps; aesop;
      · have h_step : PDA.Reaches₁ (⟨Sum.inl q, [], some Z :: (List.map some γ ++ [none])⟩ : PDA.conf (PDA_FS_to_ES_pda M)) (⟨Sum.inr 1, [], List.map some γ ++ [none]⟩ : PDA.conf (PDA_FS_to_ES_pda M)) := by
          constructor;
          swap;
          exact Sum.inr 1;
          simp +decide [ PDA_FS_to_ES_pda, PDA_FS_to_ES_eps ];
          assumption;
        exact .single h_step |> Relation.ReflTransGen.trans <| drain_reaches M _;
    use Sum.inr 1, h_path |> fun h => h_lift.trans h |> fun h => h |> fun h => by tauto;
  cases h ; aesop

/-
PROBLEM
Reverse one-step simulation: if M' takes one step between lifted configurations,
    then M takes one step between the corresponding configurations.

PROVIDED SOLUTION
PDA.Reaches₁ means r₂ ∈ PDA.step r₁ in PDA_FS_to_ES_pda M.

Case split on γ₁:

Case γ₁ = []: Stack is []. step returns ∅. So h is impossible (False.elim).

Case γ₁ = Z :: γ₁': Stack is (some Z) :: γ₁'.map some.

  Subcase w₁ = []:
    step gives transitions via transition_fun'. PDA_FS_to_ES_eps M (Sum.inl q₁) (some Z) = image of M.transition_fun' q₁ Z ∪ drain.
    Target is Sum.inl q₂, so it's from the image part: ∃ (p', β') ∈ M.transition_fun' q₁ Z with Sum.inl p' = Sum.inl q₂ and output = β'.map some.
    So q₂ = p', and new stack = β'.map some ++ γ₁'.map some = (β' ++ γ₁').map some = γ₂.map some.
    By List.map_injective (Option.some is injective), γ₂ = β' ++ γ₁'.
    In M: Reaches₁ ⟨q₁, [], Z :: γ₁'⟩ ⟨q₂, [], γ₂⟩ because (q₂, β') ∈ M.transition_fun' q₁ Z. ✓

  Subcase w₁ = a :: w₁':
    step gives transitions from transition_fun and transition_fun'.

    If from transition_fun: PDA_FS_to_ES_trans M (Sum.inl q₁) a (some Z) = image of M.transition_fun q₁ a Z.
    Target is Sum.inl q₂ with w₂ = w₁', so from image: ∃ (p', β') with Sum.inl p' = Sum.inl q₂, output = β'.map some. Then q₂ = p', γ₂ = β' ++ γ₁'. In M: Reaches₁. ✓

    If from transition_fun': similar to w₁ = [] case, but w₂ = a :: w₁'. ✓

Key: List.map_append_injective to deduce γ₂ from β'.map some ++ γ₁'.map some = γ₂.map some.
-/
lemma reverse_simulation_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (q₁ q₂ : Q) (w₁ w₂ : List T) (γ₁ γ₂ : List S)
    (h : @PDA.Reaches₁ (Q ⊕ Fin 2) T (Option S) _ _ _ (PDA_FS_to_ES_pda M)
      ⟨Sum.inl q₁, w₁, γ₁.map some⟩ ⟨Sum.inl q₂, w₂, γ₂.map some⟩) :
    @PDA.Reaches₁ Q T S _ _ _ M ⟨q₁, w₁, γ₁⟩ ⟨q₂, w₂, γ₂⟩ := by
  unfold Reaches₁ at *;
  unfold PDA.step at *; rcases w₁ with ( _ | ⟨ a, w₁ ⟩ ) <;> simp_all +decide [ Set.ext_iff ] ;
  · rcases γ₁ with ( _ | ⟨ Z, γ₁ ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda ];
    rcases h with ⟨ β, hβ, rfl, hβ' ⟩ ; simp_all +decide [ PDA_FS_to_ES_eps ] ;
    -- Since some is injective, the equality of the maps implies the equality of the original lists.
    have h_inj : Function.Injective (some : S → Option S) := by
      exact Option.some_injective _;
    have h_eq : List.map some γ₂ = List.map some (hβ.choose ++ γ₁) := by
      convert hβ' using 1 ; simp +decide [ hβ.choose_spec.2 ];
    exact ⟨ _, hβ.choose_spec.1, List.map_injective_iff.mpr h_inj h_eq ⟩;
  · rcases γ₁ with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda, PDA_FS_to_ES_eps, PDA_FS_to_ES_trans ];
    rcases h with ( ⟨ β, h₁, rfl, h₂ ⟩ | ⟨ β, h₁, rfl, h₂ ⟩ ) <;> [ left; right ] <;> use β <;> simp_all +decide [ List.map_append ];
    · exact List.map_injective_iff.mpr ( Option.some_injective _ ) <| by simpa using h₂;
    · exact List.map_injective_iff.mpr ( Option.some_injective _ ) ( by simpa using h₂ )

/-- Backward direction of PDA_FS_subset_ES. -/
lemma PDA_FS_to_ES_backward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack) :
    w ∈ M.acceptsByFinalState := by
  sorry

/-- Any PDA final-state language is also a PDA empty-stack language. -/
theorem PDA_FS_subset_ES {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    is_PDA M.acceptsByFinalState := by
  refine ⟨Q ⊕ Fin 2, Option S, inferInstance, inferInstance, PDA_FS_to_ES_pda M, ?_⟩
  ext w
  exact ⟨PDA_FS_to_ES_backward M w, PDA_FS_to_ES_forward M w⟩

end PDA_FS_to_ES

theorem is_CF_of_is_DCFL {L : Language T} (h : is_DCFL L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA (PDA_FS_subset_ES M.toPDA)

-- ============================================================================
-- DCFL complement closure
-- ============================================================================

/-- **DCFL Complement Closure**: The class of deterministic context-free languages is
    closed under complementation.

    Given a DPDA `M` accepting `L`, one constructs a new DPDA accepting `Lᶜ` by:
    (1) making `M` process all input (no infinite ε-loops, no stuck configurations),
    (2) tracking whether an accepting state is visited during post-input ε-transitions, and
    (3) accepting when the original machine would reject, and vice versa.

    This is a non-trivial construction due to Hopcroft and Ullman (1979).
    See the module docstring for the full proof sketch. -/
theorem is_DCFL_compl {L : Language T} (h : is_DCFL L) : is_DCFL Lᶜ := by
  sorry

-- ============================================================================
-- Consequence: If all CFLs were DCFLs, CFLs would be closed under complement
-- ============================================================================

/-- If every CFL (over a fixed finite alphabet `T`) were a DCFL, then every CFL's
    complement would also be a CFL. -/
theorem complement_CF_of_all_CF_DCFL {T : Type} [Fintype T]
    (h : ∀ L : Language T, is_CF L → is_DCFL L) :
    ∀ L : Language T, is_CF L → is_CF Lᶜ :=
  fun L hCF => is_CF_of_is_DCFL (is_DCFL_compl (h L hCF))

-- ============================================================================
-- Main result: There exist CFLs that are not DCFLs (DCFL ⊊ CFL)
-- ============================================================================

/-- There exist context-free languages over `Fin 3` that are not deterministic context-free. -/
theorem exists_CF_not_DCFL : ∃ L : Language (Fin 3), is_CF L ∧ ¬ is_DCFL L := by
  sorry

-- ============================================================================
-- The explicit witness: {aⁱ bʲ cᵏ | i = j ∨ j = k}
-- ============================================================================

section explicit_witness

/-- The language `{aⁿ bⁿ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbnck : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate n 1 ++ List.replicate m 2

/-- The language `{aⁿ bᵐ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbmcm : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate m 1 ++ List.replicate m 2

/-- The language `{aⁱ bʲ cᵏ | i = j ∨ j = k}` over `{0, 1, 2}`.
    The standard explicit witness of a CFL that is not a DCFL. -/
def lang_aibjck : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ (i = j ∨ j = k)

/-- `lang_aibjck` equals the union of `lang_anbnck` and `lang_anbmcm`. -/
theorem lang_aibjck_eq_union : lang_aibjck = lang_anbnck + lang_anbmcm := by
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro ⟨i, j, k, hw, hij | hjk⟩
    · left; exact ⟨i, k, hij ▸ hw⟩
    · right; exact ⟨i, j, hjk ▸ hw⟩
  · rintro (⟨n, m, hw⟩ | ⟨n, m, hw⟩)
    · exact ⟨n, n, m, hw, Or.inl rfl⟩
    · exact ⟨n, m, m, hw, Or.inr rfl⟩

/-- `{aⁿ bⁿ cᵐ}` is context-free. -/
theorem is_CF_lang_anbnck : is_CF lang_anbnck :=
  sorry

/-- `{aⁿ bᵐ cᵐ}` is context-free. -/
theorem is_CF_lang_anbmcm : is_CF lang_anbmcm :=
  sorry

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is context-free. -/
theorem lang_aibjck_CFL : is_CF lang_aibjck := by
  rw [lang_aibjck_eq_union]
  exact CF_of_CF_u_CF _ _ ⟨is_CF_lang_anbnck, is_CF_lang_anbmcm⟩

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is NOT a deterministic context-free language.

    **Proof sketch.** If this language were DCFL, its complement would be DCFL (by
    `is_DCFL_compl`), hence CFL (by `is_CF_of_is_DCFL`). The complement intersected
    with the regular language `a*b*c*` yields `{aⁱ bʲ cᵏ | i ≠ j ∧ j ≠ k}`. Since
    CFL ∩ regular = CFL (`CF_of_CF_inter_regular`), this language would be CFL. But
    `{aⁱ bʲ cᵏ | i ≠ j ∧ j ≠ k}` is NOT context-free (provable by Ogden's lemma),
    giving a contradiction. -/
theorem not_DCFL_lang_aibjck : ¬ is_DCFL lang_aibjck := by
  sorry

end explicit_witness
