module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
public import Mathlib.Data.Matrix.Mul
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Closure.IntersectionRegular
import Langlib.Classes.ContextFree.Closure.Star
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Grammars.ContextFree.MathlibCFG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Context-Free Closure Under Inverse String Homomorphism

This file proves that context-free languages are closed under inverse string
homomorphism. Given a CFL `L` over `β` and a string homomorphism `h : α → List β`,
the preimage `h⁻¹(L) = {w : List α | h(w) ∈ L}` is also context-free.

## Strategy

We decompose `h⁻¹(L)` as `π(D ∩ f⁻¹(L))` where the intermediate alphabet is `Γ = α ⊕ β`:

- `fHom : Γ → List β` erases `Sum.inl` symbols and unwraps `Sum.inr` symbols.
- `piHom : Γ → List α` keeps `Sum.inl` values and erases `Sum.inr` symbols.
- `dLang` is a regular "well-formedness" language over `Γ` consisting of valid encodings.
- `fInv L` is CFL (the language `L` with `Sum.inl` symbols freely inserted).

Then:
- `fInv L` is CFL via substitution (`CF_of_subst_CF`).
- `dLang h` is regular via DFA construction.
- `dLang h ∩ fInv L` is CFL (`CF_of_CF_inter_regular`).
- `π(dLang h ∩ fInv L)` is CFL (`CF_closed_under_homomorphism`).

## Main declarations

- `Language.inverseHomomorphicImage` : the preimage of a language under a string homomorphism.
- `CF_closed_under_inverse_homomorphism` : CFLs are closed under inverse homomorphism.
-/

open Classical

noncomputable section

variable {α β : Type}

/-- Extend a homomorphism to words by concatenation. -/
def extendHom (h : α → List β) (w : List α) : List β :=
  (w.map h).flatten

-- ============================================================================
-- §1. Definition of inverse homomorphic image
-- ============================================================================

/-- The preimage of a language `L` under a string homomorphism `h`.
This is the set of words `w` over `α` such that `h(w) ∈ L`, where `h` extends to words by
concatenation: `h(a₁⋯aₙ) = h(a₁) ++ ⋯ ++ h(aₙ)`. -/
def Language.inverseHomomorphicImage (L : Language β) (h : α → List β) : Language α :=
  {w : List α | extendHom h w ∈ L}

-- ============================================================================
-- §2. Intermediate alphabet and helper maps
-- ============================================================================

/-- Embed a symbol `a` into `Γ = α ⊕ β` as `[inl a] ++ (h a).map inr`. -/
def embedWord (h : α → List β) (a : α) : List (α ⊕ β) :=
  [Sum.inl a] ++ (h a).map Sum.inr

/-- Project `Γ` to `β`: erase `inl`, unwrap `inr`. -/
def fHom : α ⊕ β → List β
  | Sum.inl _ => []
  | Sum.inr b => [b]

/-- Project `Γ` to `α`: keep `inl`, erase `inr`. -/
def piHom : α ⊕ β → List α
  | Sum.inl a => [a]
  | Sum.inr _ => []

lemma embedWord_flatMap_fHom (h : α → List β) (a : α) :
    (embedWord h a).flatMap fHom = h a := by
      unfold embedWord
      simp [fHom];
      induction h a <;> aesop

/-
Composing `embedWord` then `fHom` gives `h`.
-/
lemma extendHom_eq_flatMap_embedWord_fHom (h : α → List β) (w : List α) :
    extendHom h w = (extendHom (embedWord h) w).flatMap fHom := by
      unfold extendHom;
      induction w <;> simp +decide [ List.flatMap ] at *;
      rename_i k hk ih; rw [ ← ih ] ;
      exact congr_arg₂ _ ( embedWord_flatMap_fHom h k |> Eq.symm ) rfl

lemma embedWord_flatMap_piHom (h : α → List β) (a : α) :
    (embedWord h a).flatMap piHom = [a] := by
      -- By definition of `embedWord` and `piHom`, we can simplify the expression.
      simp [embedWord, piHom]

/-
Composing `embedWord` then `piHom` is the identity.
-/
lemma extendHom_embedWord_piHom (h : α → List β) (w : List α) :
    (extendHom (embedWord h) w).flatMap piHom = w := by
  induction w with
  | nil => simp [extendHom]
  | cons a w ih =>
      simp [extendHom, embedWord_flatMap_piHom]
      simpa [extendHom] using ih

-- ============================================================================
-- §3. The language S of single inl-symbol words
-- ============================================================================

/-- `S = {[inl a] | a ∈ α}`, the set of single-symbol `inl` words. -/
def sLang (α β : Type) : Language (α ⊕ β) :=
  {w | ∃ a : α, w = [Sum.inl a]}

/-
`sLang` is CFL when `α` is finite.
-/
lemma is_CF_sLang [Fintype α] : is_CF (sLang α β) := by
  by_contra! h_contra;
  have h_cfl_singleton : ∀ a : α, is_CF ({[Sum.inl a]} : Language (α ⊕ β)) := by
    exact fun a => is_CF_singleton [Sum.inl a];
  have h_cfl_union : ∀ (s : Finset α), is_CF (⋃ a ∈ s, {[Sum.inl a]} : Language (α ⊕ β)) := by
    intro s
    induction' s using Finset.induction with a s ih;
    · -- The empty language is context-free because it can be generated by a context-free grammar with no rules.
      use ⟨Unit, (), []⟩;
      simp +decide [ grammar_context_free, grammar_language ];
      ext w; simp [setOf];
      unfold grammar_generates; simp +decide ;
      constructor <;> intro h <;> cases w <;> simp_all +decide [ grammar_derives ];
      · cases h;
        cases ‹_› ; aesop;
      · cases h;
        cases ‹grammar_transforms _ _ _› ; aesop;
      · contradiction;
      · contradiction;
    · simp_all +decide [  ];
      have h_cfl_union : is_CF ({[Sum.inl a]} : Language (α ⊕ β)) ∧ is_CF (⋃ a ∈ s, {[Sum.inl a]} : Language (α ⊕ β)) := by
        aesop;
      convert Language.IsContextFree.add _ _ using 1;
      · ext;
        exact is_CF_iff_isContextFree;
      · convert isContextFree_singleton [ Sum.inl a ] using 1;
      · convert h_cfl_union.2 using 1;
        ext; simp [is_CF_iff_isContextFree];
  apply h_contra;
  convert h_cfl_union Finset.univ;
  ext; simp [sLang];
  exact ⟨ fun ⟨ a, ha ⟩ => ⟨ a, ha.symm ⟩, fun ⟨ a, ha ⟩ => ⟨ a, ha.symm ⟩ ⟩

-- ============================================================================
-- §4. f⁻¹(L) is CFL
-- ============================================================================

/-- `f⁻¹(L) = {v : List Γ | v.flatMap fHom ∈ L}`. -/
def fInv (L : Language β) : Language (α ⊕ β) :=
  {v | List.flatMap fHom v ∈ L}

/-- `σ(b) = S* · {[inr b]}`. -/
def substFn (α : Type) (β : Type) (b : β) : Language (α ⊕ β) :=
  KStar.kstar (sLang α β) * {[Sum.inr b]}

/-
A list of inl-symbols belongs to S*.
-/
lemma allInl_mem_kstar_sLang (v : List (α ⊕ β)) (hv : ∀ x ∈ v, x.isLeft) :
    v ∈ KStar.kstar (sLang α β) := by
      induction' v with x v ih;
      · exact ⟨ [ ], by simp +decide ⟩;
      · cases x <;> simp_all +decide [ KStar.kstar ];
        obtain ⟨ L, rfl, hL ⟩ := ih;
        -- Let's construct the list L' by prepending [Sum.inl val✝] to L.
        use [ [Sum.inl ‹_›] ] ++ L;
        simp_all +decide [ sLang ];
        exact ⟨ _, rfl ⟩

/-
flatMap fHom over a list of all-inl symbols is [].
-/
private lemma flatMap_fHom_allInl (v : List (α ⊕ β)) (hv : ∀ x ∈ v, x.isLeft) :
    List.flatMap fHom v = [] := by
      induction v <;> aesop

/-
flatMap fHom over kstar sLang is [].
-/
lemma flatMap_fHom_kstar_sLang (v : List (α ⊕ β)) (hv : v ∈ KStar.kstar (sLang α β)) :
    List.flatMap fHom v = [] := by
      cases isEmpty_or_nonempty α <;> cases isEmpty_or_nonempty β <;> simp_all +decide [ KStar.kstar ];
      · obtain ⟨ L, rfl, hL ⟩ := hv; induction L <;> simp_all +decide [ sLang ] ;
        tauto;
      · exact fun a a_1 => Eq.symm ((fun {α} {xs} => List.nil_eq.mpr) rfl);
      · obtain ⟨ L, rfl, hL ⟩ := hv;
        constructor <;> intro x hx <;> contrapose! hx <;> simp_all +decide [ sLang ];
        · cases hx rfl;
        · grind +revert

/-
A word in substFn α β b has flatMap fHom equal to [b].
-/
lemma flatMap_fHom_substFn (v : List (α ⊕ β)) (b : β) (hv : v ∈ substFn α β b) :
    List.flatMap fHom v = [b] := by
      obtain ⟨ u, hu, w, hw, rfl ⟩ := hv;
      rcases hw with rfl; simp +decide [ flatMap_fHom_kstar_sLang u hu ] ;
      rfl

/-
Decompose a List (α ⊕ β) into alternating inl-blocks and inr-symbols.
    Every word v can be written as s₀ ++ [inr b₁] ++ s₁ ++ ... ++ [inr bₖ] ++ sₖ
    where each sᵢ consists only of inl-symbols.
-/
lemma decompose_sum_list (v : List (α ⊕ β)) :
    ∃ (bs : List β) (ss : List (List (α ⊕ β))),
      ss.length = bs.length + 1 ∧
      (∀ s ∈ ss, ∀ x ∈ s, x.isLeft) ∧
      v = (List.zipWith (fun s b => s ++ [Sum.inr b]) ss.dropLast bs).flatten ++ ss.getLast! ∧
      List.flatMap fHom v = bs := by
        have h_ind : ∀ (v : List (α ⊕ β)), ∃ (bs : List β) (ss : List (List (α ⊕ β))), ss.length = bs.length + 1 ∧ (∀ s ∈ ss, ∀ x ∈ s, x.isLeft) ∧ List.flatMap fHom v = bs ∧ v = (List.zipWith (fun s b => s ++ [Sum.inr b]) ss.dropLast bs).flatten ++ ss.getLast! := by
          intro v
          induction' v with x rest ih;
          · exact ⟨ [ ], [ [ ] ], rfl, by simp +decide ⟩;
          · rcases ih with ⟨ bs, ss, h₁, h₂, h₃, h₄ ⟩ ; rcases x with ( x | x ) <;> simp_all +decide [ List.flatMap ] ;
            · rcases ss with ( _ | ⟨ s, _ | ⟨ t, ss ⟩ ⟩ ) <;> simp_all +decide [ List.getLast? ];
              · use [ [ Sum.inl x ] ++ s ] ; aesop;
              · refine' ⟨ ( Sum.inl x :: s ) :: t :: ss, _, _, _ ⟩ <;> simp_all +decide [ fHom ];
                cases bs <;> aesop;
            · refine' ⟨ [ [] ] ++ ss, _, _, _ ⟩ <;> simp_all +decide [  ];
              · exact Nat.add_comm bs.length 1;
              · cases ss <;> aesop;
        exact Exists.imp ( by tauto ) ( h_ind v )

/-
`f⁻¹(L) = (L.subst σ) · S*`.
-/
lemma fInv_eq (L : Language β) :
    (fInv L : Language (α ⊕ β)) =
    (L.subst (substFn α β)) * KStar.kstar (sLang α β) := by
      ext u; constructor <;> intro hu;
      · obtain ⟨ bs, ss, hss₁, hss₂, rfl, hss₃ ⟩ := decompose_sum_list u;
        refine' ⟨ _, _, _ ⟩;
        exact ( List.zipWith ( fun s b => s ++ [ Sum.inr b ] ) ss.dropLast bs ).flatten;
        · refine' ⟨ bs, _, _ ⟩;
          · exact hss₃ ▸ hu;
          · rw [ Language.mem_list_prod_iff_forall2 ];
            refine' ⟨ List.zipWith ( fun s b => s ++ [ Sum.inr b ] ) ss.dropLast bs, _, _ ⟩ <;> simp_all +decide [ List.forall₂_iff_get ];
            intro i hi; exact (by
            refine' ⟨ _, _, _ ⟩;
            exact ss[i];
            · apply allInl_mem_kstar_sLang;
              grind;
            · exact ⟨ _, Set.mem_singleton _, rfl ⟩);
        · refine' ⟨ ss.getLast!, _, rfl ⟩;
          apply allInl_mem_kstar_sLang;
          grind;
      · obtain ⟨ v, hv, w, hw, rfl ⟩ := hu;
        obtain ⟨ w', hw', hv' ⟩ := hv;
        have h_flatMap : List.flatMap fHom v = w' := by
          have hv_flatMap : ∀ {w : List β} {v : List (α ⊕ β)}, v ∈ (w.map (substFn α β)).prod → v.flatMap fHom = w := by
            intros w v hv; induction' w with b w ih generalizing v <;> simp_all +decide [ List.map ] ;
            obtain ⟨ v₁, hv₁, v₂, hv₂, rfl ⟩ := hv;
            have := flatMap_fHom_substFn v₁ b hv₁; aesop;
          exact hv_flatMap hv';
        have h_flatMap_w : List.flatMap fHom w = [] := by
          exact flatMap_fHom_kstar_sLang w hw;
        grind +locals

/-- `f⁻¹(L)` is CFL when `L` is CFL and `α` is finite. -/
lemma is_CF_fInv [Fintype α] (L : Language β) (hL : is_CF L) :
    is_CF (fInv L : Language (α ⊕ β)) := by
  rw [fInv_eq]
  exact CF_of_CF_c_CF _ _ ⟨
    CF_of_subst_CF L (substFn α β) hL (fun b =>
      CF_of_CF_c_CF _ _ ⟨CF_of_star_CF _ is_CF_sLang, is_CF_singleton _⟩),
    CF_of_star_CF _ is_CF_sLang⟩

-- ============================================================================
-- §5. D is regular
-- ============================================================================

/-- `D = (⋃_a {embedWord h a})*`, the set of valid encodings. -/
def dLang (h : α → List β) : Language (α ⊕ β) :=
  KStar.kstar {w | ∃ a : α, w = embedWord h a}

/-- DFA state type for recognizing `D`.
- `none`: dead state
- `some none`: ready/accepting state (completed all blocks)
- `some (some ⟨a, k⟩)`: currently processing `h(a)` at position `k` -/
abbrev DFAState (α β : Type) (h : α → List β) :=
  Option (Option (Σ a : α, Fin (h a).length))

/-- DFA transition function for recognizing `D`. -/
def dStep (h : α → List β) : DFAState α β h → (α ⊕ β) → DFAState α β h
  | some none, Sum.inl a =>
      if hl : 0 < (h a).length then some (some ⟨a, ⟨0, hl⟩⟩)
      else some none
  | some (some ⟨a, k⟩), Sum.inr b =>
      if (h a).get k = b then
        if hlast : k.val + 1 < (h a).length then some (some ⟨a, ⟨k.val + 1, hlast⟩⟩)
        else some none
      else none
  | some none, Sum.inr _ => none
  | some (some _), Sum.inl _ => none
  | none, _ => none

/-- The DFA recognizing `D`. -/
def invHomDFA (h : α → List β) : DFA (α ⊕ β) (DFAState α β h) where
  step := dStep h
  start := some none
  accept := {some none}

/-
Processing a single embedWord block from the ready state returns to ready.
-/
lemma dStep_embedWord (h : α → List β) (a : α) :
    (embedWord h a).foldl (dStep h) (some none) = some none := by
      -- By induction on the length of `h a`, we can show that processing the list of `Sum.inr` elements brings us back to `some none`.
      have h_ind : ∀ (k : ℕ) (hk : k ≤ (h a).length), List.foldl (dStep h) (if hl : 0 < (h a).length then if hl : k < (h a).length then some (some ⟨a, ⟨k, hl⟩⟩) else some none else some none) (List.map Sum.inr (List.drop k (h a))) = some none := by
        intro k hk; induction' m : ( h a ).length - k with m ih generalizing k <;> simp_all +decide [  ] ;
        · cases eq_or_lt_of_le hk <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
          simp +decide [ List.drop_eq_nil_of_le ];
        · rcases eq_or_lt_of_le hk <;> simp_all +decide [  ];
          rw [ show List.drop k ( List.map Sum.inr ( h a ) ) = Sum.inr ( ( h a ).get ⟨ k, by linarith ⟩ ) :: List.drop ( k + 1 ) ( List.map Sum.inr ( h a ) ) from ?_ ];
          · split_ifs <;> simp_all +decide [ dStep ];
            grind;
          · grind +suggestions;
      specialize h_ind 0 ; aesop

/-- foldl dStep distributes over concatenation. -/
private lemma foldl_dStep_append (h : α → List β) (v w : List (α ⊕ β)) (s : DFAState α β h) :
    (v ++ w).foldl (dStep h) s = w.foldl (dStep h) (v.foldl (dStep h) s) := by
  exact List.foldl_append

/-
Processing a word from dead state stays dead.
-/
lemma foldl_dStep_none (h : α → List β) (v : List (α ⊕ β)) :
    v.foldl (dStep h) none = none := by
      induction v <;> aesop

/-
Backward: if v ∈ dLang h, then the DFA accepts v.
-/
lemma dfa_accepts_of_dLang (h : α → List β) (v : List (α ⊕ β)) (hv : v ∈ dLang h) :
    v.foldl (dStep h) (some none) = some none := by
      obtain ⟨ws, hv_eq, hws⟩ : ∃ ws : List (List (α ⊕ β)), v = ws.flatten ∧ ∀ w ∈ ws, ∃ a : α, w = embedWord h a := by
        convert hv using 1;
      -- By induction on the list `ws`, we can show that the foldl of `dStep h` on the flattened list of `ws` is `some none`.
      have h_ind : ∀ ws : List (List (α ⊕ β)), (∀ w ∈ ws, ∃ a : α, w = embedWord h a) → List.foldl (dStep h) (some none) (List.flatten ws) = some none := by
        intro ws hws;
        induction' ws using List.reverseRecOn with ws ih;
        · rfl;
        · simp_all +decide [ List.foldl_append ];
          obtain ⟨ a, rfl ⟩ := hws _ ( Or.inr rfl ) ; exact dStep_embedWord h a;
      rw [ hv_eq, h_ind ws hws ]

/-
From state mid a k, if foldl reaches some none, then the input starts with
    the remaining suffix of (h a).map inr and the rest is accepted from ready.
-/
lemma dfa_mid_consume (h : α → List β) (a : α) (k : Fin (h a).length) (v : List (α ⊕ β))
    (hv : v.foldl (dStep h) (some (some ⟨a, k⟩)) = some none) :
    ∃ rest, v = ((h a).drop k.val).map Sum.inr ++ rest ∧
      rest.foldl (dStep h) (some none) = some none := by
        induction' n : ( h a |> List.length ) - k using Nat.strong_induction_on with n ih generalizing k v;
        rcases v with ( _ | ⟨ x, v ⟩ ) <;> simp_all +decide [ List.foldl ];
        rcases x with ( x | x ) <;> simp_all +decide [ dStep ];
        · exact absurd hv ( by rw [ foldl_dStep_none ] ; simp +decide );
        · split_ifs at hv <;> simp_all +decide [ List.drop_eq_getElem_cons ];
          · grind;
          · rw [ List.drop_eq_nil_of_le ] <;> aesop;
          · exact absurd hv ( by rw [ foldl_dStep_none ] ; simp +decide )

/-
Forward: if the DFA accepts v, then v ∈ dLang h.
-/
lemma dLang_of_dfa_accepts (h : α → List β) (v : List (α ⊕ β))
    (hv : v.foldl (dStep h) (some none) = some none) :
    v ∈ dLang h := by
      induction' n : v.length using Nat.strong_induction_on with n ih generalizing v;
      rcases v with ( _ | ⟨ x, v ⟩ ) <;> simp_all +decide [ dStep ];
      · constructor;
        swap;
        exacts [ [ ], by simp +decide ];
      · rcases x with ( a | b ) <;> simp_all +decide [  ];
        · split_ifs at hv <;> simp_all +decide [ dLang ];
          · obtain ⟨ rest, hrest₁, hrest₂ ⟩ := dfa_mid_consume h a ⟨ 0, by linarith ⟩ v hv;
            specialize ih ( List.length rest ) ( by simp +arith +decide [ hrest₁ ] at *; linarith ) rest hrest₂ rfl ; simp_all +decide [ KStar.kstar ] ;
            obtain ⟨ L, rfl, hL ⟩ := ih; use [ embedWord h a ] ++ L; simp +decide [ embedWord ] ;
            exact ⟨ ⟨ a, rfl ⟩, fun x hx => by obtain ⟨ a', rfl ⟩ := hL x hx; exact ⟨ a', rfl ⟩ ⟩;
          · have := ih _ ( by linarith ) _ hv rfl; simp_all +decide [ KStar.kstar ] ;
            obtain ⟨ L, rfl, hL ⟩ := this; use [ [ Sum.inl a ] ] ++ L; simp_all +decide [ embedWord ] ;
            exact ⟨ a, by simp +decide [ * ] ⟩;
        · exact absurd hv ( by erw [ foldl_dStep_none ] ; simp +decide )

/-- Correctness: the DFA accepts exactly `D`. -/
lemma invHomDFA_correct (h : α → List β) :
    (invHomDFA h).accepts = dLang h := by
  ext v
  simp [DFA.accepts, invHomDFA]
  exact ⟨dLang_of_dfa_accepts h v, dfa_accepts_of_dLang h v⟩

/-- `D` is a regular language when `α` is finite. -/
lemma isRegular_dLang [Fintype α] (h : α → List β) :
    (dLang h).IsRegular := by
  rw [Language.isRegular_iff]
  exact ⟨DFAState α β h, inferInstance, invHomDFA h, invHomDFA_correct h⟩

/-
============================================================================
§6. Main identity
============================================================================

`h⁻¹(L) = π(D ∩ f⁻¹(L))`.
-/
lemma inverseHomomorphicImage_eq (L : Language β) (h : α → List β) :
    L.inverseHomomorphicImage h =
    ((fInv L ⊓ dLang h) : Language (α ⊕ β)).homomorphicImage piHom := by
      ext w
      simp [Language.inverseHomomorphicImage, Language.homomorphicImage];
      constructor;
      · intro hw
        use extendHom (embedWord h) w;
        refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
        · convert hw using 1;
          rw [ extendHom_eq_flatMap_embedWord_fHom ];
          rw [ show extendHom ( embedWord ( embedWord h ) ) w = List.flatMap ( fun a => embedWord ( embedWord h ) a ) w from rfl ];
          rw [ show List.flatMap fHom ( List.flatMap ( fun a => embedWord ( embedWord h ) a ) w ) = List.flatMap ( fun a => List.flatMap fHom ( embedWord ( embedWord h ) a ) ) w from ?_ ];
          · simp +decide [ fHom, embedWord ];
            rw [ show List.flatMap ( fun a => Sum.inl a :: List.flatMap fHom ( List.map ( Sum.inr ∘ Sum.inr ) ( h a ) ) ) w = List.flatMap ( fun a => Sum.inl a :: List.map ( fun b => Sum.inr b ) ( h a ) ) w from ?_ ];
            · simp +decide [ fInv, extendHom ];
              rw [ show List.flatMap fHom ( List.flatMap ( fun a => Sum.inl a :: List.map ( fun b => Sum.inr b ) ( h a ) ) w ) = List.flatMap ( fun a => List.flatMap fHom ( Sum.inl a :: List.map ( fun b => Sum.inr b ) ( h a ) ) ) w from ?_ ];
              · simp +decide [ fHom ];
                rw [ show List.flatMap ( fun a => List.flatMap fHom ( List.map ( fun b => Sum.inr b ) ( h a ) ) ) w = List.flatMap ( fun a => h a ) w from ?_ ];
                · rfl;
                · congr! 2;
                  induction ( h ‹_› ) <;> aesop;
              · rw [ List.flatMap_assoc ];
            · congr! 2;
              induction ( h ‹_› ) <;> aesop;
          · rw [ List.flatMap_assoc ];
        · -- By definition of `dLang`, we need to show that `extendHom (embedWord h) w` is a concatenation of blocks from `dLang h`.
          simp [dLang];
          induction w <;> simp_all +decide [ KStar.kstar ];
          · exact ⟨ [ ], rfl, by tauto ⟩;
          · use [embedWord h ‹_›] ++ List.map (fun a => embedWord h a) ‹List α›; simp [extendHom];
            exact ⟨ ⟨ _, rfl ⟩, fun a ha => ⟨ _, rfl ⟩ ⟩;
        · have h_flatMap : (extendHom (embedWord h) w).flatMap piHom = w := by
            exact extendHom_embedWord_piHom h w;
          rw [ ← h_flatMap, Language.mem_list_prod_iff_forall2 ];
          grind +suggestions;
      · rintro ⟨ v, hv₁, hv₂ ⟩;
        -- By definition of $dLang$, we know that $v$ is a concatenation of $embedWord$ blocks.
        obtain ⟨w', hw'⟩ : ∃ w' : List α, v = extendHom (embedWord h) w' := by
          have hv₃ : v ∈ dLang h := by
            exact hv₁.2;
          obtain ⟨w', hw'⟩ : ∃ w' : List (List (α ⊕ β)), v = w'.flatten ∧ List.Forall₂ (fun w s => ∃ a : α, w = embedWord h a) w' (List.replicate (List.length w') ()) := by
            have hv₃ : v ∈ {w | ∃ w' : List (List (α ⊕ β)), v = w'.flatten ∧ List.Forall₂ (fun w s => ∃ a : α, w = embedWord h a) w' (List.replicate (List.length w') ())} := by
              have := hv₃
              obtain ⟨ L, rfl, hL ⟩ := this;
              refine' ⟨ L, rfl, _ ⟩;
              rw [ List.forall₂_iff_get ];
              aesop;
            exact hv₃;
          have hw'_eq : ∀ {w' : List (List (α ⊕ β))}, List.Forall₂ (fun w s => ∃ a : α, w = embedWord h a) w' (List.replicate (List.length w') ()) → ∃ w'' : List α, w' = List.map (fun a => embedWord h a) w'' := by
            intros w' hw'; induction' w' with w' ih <;> simp_all +decide [  ] ;
            simp_all +decide [ List.replicate ];
            rcases hw'.1 with ⟨ a, rfl ⟩ ; rcases ‹∃ w'', ih = List.map ( fun a => embedWord h a ) w''› with ⟨ w'', rfl ⟩ ; exact ⟨ a :: w'', by simp +decide ⟩ ;
          obtain ⟨ w'', rfl ⟩ := hw'_eq hw'.2; use w''; aesop;
        have h_w_eq_w' : w = w' := by
          have h_w_eq_w' : List.flatMap piHom v = w := by
            rw [Language.mem_list_prod_iff_forall2] at hv₂;
            obtain ⟨ W, rfl, hW ⟩ := hv₂;
            have hW_eq : W = List.map (fun a => piHom a) v := by
              rw [ List.forall₂_iff_get ] at hW;
              refine' List.ext_get _ _ <;> aesop;
            aesop;
          rw [ ← h_w_eq_w', hw', extendHom_embedWord_piHom ];
        rw [h_w_eq_w'] at *
        have hvL : (extendHom (embedWord h) w').flatMap fHom ∈ L := by
          rw [hw'] at hv₁
          simpa [fInv] using hv₁.1
        change extendHom h w' ∈ L
        rw [extendHom_eq_flatMap_embedWord_fHom h w']
        exact hvL

-- ============================================================================
-- §7. Main theorem
-- ============================================================================

/-- The class of context-free languages is closed under inverse string homomorphism.

Given a context-free language `L` over alphabet `β` and a string homomorphism `h : α → List β`
(with `α` a finite type), the preimage `h⁻¹(L) = {w | h(w) ∈ L}` is also context-free. -/
theorem CF_closed_under_inverse_homomorphism [Fintype α]
    (L : Language β) (h : α → List β) (hL : is_CF L) :
    is_CF (L.inverseHomomorphicImage h) := by
  rw [inverseHomomorphicImage_eq]
  apply CF_closed_under_homomorphism
  apply CF_of_CF_inter_regular
  · exact is_CF_fInv L hL
  · exact isRegular_dLang h

/-- The class of context-free languages is closed under inverse string homomorphism. -/
theorem CF_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_CF := by
  intro α β _ _ L h hL
  simpa [Language.inverseHomomorphicImage] using
    CF_closed_under_inverse_homomorphism (α := α) (β := β) L h hL

end
