import Mathlib
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Examples.TopBot
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Under Prefix

This file proves that regular languages are closed under the prefix operation
and shows that the converse fails over any nontrivial alphabet.

## Main declarations

- `DFA.reachableAccept`
- `DFA.prefixDFA`
- `Language.IsRegular.prefixLang`
- `Language.not_iff_regular_prefix`
-/

open List Set Computability

namespace DFA

variable {α : Type*} {σ : Type*}

/-- The set of states from which some accepting state is reachable. -/
def reachableAccept (M : DFA α σ) : Set σ :=
  { s : σ | ∃ x : List α, M.evalFrom s x ∈ M.accept }

/-- A DFA accepting the prefix language of the original DFA's language. -/
def prefixDFA (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.reachableAccept

theorem evalFrom_prefixDFA (M : DFA α σ) (s : σ) (x : List α) :
    M.prefixDFA.evalFrom s x = M.evalFrom s x := by
  rfl

theorem mem_prefixDFA_accept (M : DFA α σ) (s : σ) :
    s ∈ M.prefixDFA.accept ↔ ∃ x : List α, M.evalFrom s x ∈ M.accept := by
  rfl

/-- The prefix DFA accepts exactly the prefix language of the original DFA. -/
theorem prefixDFA_accepts (M : DFA α σ) :
    M.prefixDFA.accepts = Language.prefixLang M.accepts := by
  ext w
  simp only [DFA.mem_accepts, Language.mem_prefixLang, evalFrom_prefixDFA,
    mem_prefixDFA_accept, DFA.eval]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rwa [DFA.evalFrom_of_append]⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rwa [← DFA.evalFrom_of_append]⟩

end DFA

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the prefix operation. -/
theorem IsRegular.prefixLang {L : Language α} (h : L.IsRegular) :
    (prefixLang L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨σ, inferInstance, M.prefixDFA, M.prefixDFA_accepts⟩

private lemma map_anbn_compl_not_isRegular {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) : ¬ (Language.map f anbn)ᶜ.IsRegular := by
  intro h
  exact map_anbn_not_isRegular hf (Language.isRegular_compl_iff.mp h)

/-- No word of the form `w ++ [f false]` belongs to the injective image of `anbn`. -/
private lemma append_false_image_not_mem_map_anbn {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) (w : List T) :
    w ++ [f false] ∉ Language.map f anbn := by
  rintro ⟨u, ⟨n, rfl⟩, hmap⟩
  cases n with
  | zero =>
      simp at hmap
  | succ n =>
      have hrev := congr_arg List.reverse hmap
      have hhead := congr_arg List.head? hrev
      have hne : f true ≠ f false := by
        intro h
        have htf : true = false := hf h
        cases htf
      simp [List.map_append, List.reverse_append, List.replicate] at hhead
      have hrep : (List.replicate n (f true)).head?.getD (f true) = f true := by
        cases n <;> simp [List.replicate]
      exact hne (hrep.symm.trans hhead)

/-- `prefixLang((map f anbn)ᶜ) = ⊤` for injective two-symbol codings. -/
private lemma prefixLang_map_anbn_compl_eq_top {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) :
    prefixLang (Language.map f anbn)ᶜ = ⊤ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨[f false], append_false_image_not_mem_map_anbn hf w⟩

/-- The converse of prefix closure fails over any nontrivial alphabet. -/
theorem not_iff_regular_prefix [Nontrivial α] :
    ¬ (∀ (L : Language α), (prefixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let f : Bool → α := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  have hpref : (prefixLang (Language.map f anbn)ᶜ).IsRegular := by
    rw [prefixLang_map_anbn_compl_eq_top hf]
    exact isRegular_top
  exact map_anbn_compl_not_isRegular hf ((h (Language.map f anbn)ᶜ).mp hpref)

end Language
