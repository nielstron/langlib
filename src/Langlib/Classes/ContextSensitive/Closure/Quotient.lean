module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextSensitive.Decidability.Membership
import Langlib.Classes.Regular.Closure.Homomorphism
import Langlib.Grammars.ContextSensitive.Toolbox
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization
import Mathlib.Tactic

/-!
# Context-Sensitive Non-Closure Under Right Quotient

For the current `is_CS` definition, context-sensitive grammars are non-contracting and therefore
cannot generate the empty word.  This gives a small right-quotient counterexample:
`{[a]} / {[a]} = {[]}`.
-/

open Relation

variable {T : Type}

private def singletonCSGrammar (a : T) : CS_grammar T where
  nt := Unit
  initial := ()
  rules := [csrule.mk [] () [] [symbol.terminal a]]
  output_nonempty := by
    intro r hr
    simp at hr
    subst r
    simp

private lemma singletonCSGrammar_step_initial (a : T) :
    CS_transforms (singletonCSGrammar a)
      [symbol.nonterminal ()] [symbol.terminal a] := by
  refine ⟨csrule.mk [] () [] [symbol.terminal a], [], [], ?_, ?_, ?_⟩ <;>
    simp [singletonCSGrammar]

private lemma singletonCSGrammar_no_step_from_terminal (a : T)
    {w : List (symbol T (singletonCSGrammar a).nt)} :
    ¬ CS_transforms (singletonCSGrammar a) [symbol.terminal a] w := by
  rintro ⟨r, u, v, hr, hleft, _⟩
  simp [singletonCSGrammar] at hr
  subst r
  cases u <;> simp at hleft

private lemma singletonCSGrammar_terminal_derives (a : T)
    {w : List (symbol T (singletonCSGrammar a).nt)}
    (h : CS_derives (singletonCSGrammar a) [symbol.terminal a] w) :
    w = [symbol.terminal a] := by
  cases CS_tran_or_id_of_deri h with
  | inl hid => exact hid.symm
  | inr hstep =>
      obtain ⟨_, ht, _⟩ := hstep
      exact False.elim (singletonCSGrammar_no_step_from_terminal a ht)

private theorem singletonCSGrammar_language (a : T) :
    CS_language (singletonCSGrammar a) = ({[a]} : Language T) := by
  ext w
  constructor
  · intro hw
    unfold CS_language at hw
    cases CS_tran_or_id_of_deri hw with
    | inl hid =>
        cases w <;> simp [singletonCSGrammar] at hid
    | inr hstep =>
        obtain ⟨v, ht, hv⟩ := hstep
        have hv_eq : v = [symbol.terminal a] := by
          obtain ⟨r, u, v', hr, hleft, hright⟩ := ht
          simp [singletonCSGrammar] at hr
          subst r
          cases u <;> simp_all
        subst v
        have hfinal := singletonCSGrammar_terminal_derives a hv
        simpa using hfinal
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact CS_deri_of_tran (singletonCSGrammar_step_initial a)

/-- A one-letter singleton language is context-sensitive. -/
public theorem CS_singleton_letter (a : T) : is_CS ({[a]} : Language T) :=
  is_CS_via_csg_implies_is_CS ⟨singletonCSGrammar a, singletonCSGrammar_language a⟩

/-- No language containing the empty word is context-sensitive under the current definition. -/
public theorem not_CS_of_nil_mem {L : Language T} (hε : [] ∈ L) : ¬ is_CS L := by
  intro h
  obtain ⟨g, hL⟩ := is_CS_implies_is_CS_via_csg h
  have hempty : [] ∈ CS_language g := by
    rw [hL]
    exact hε
  exact empty_not_in_CS_language g hempty

/-- The current context-sensitive class does not contain the empty-word singleton. -/
public theorem not_CS_epsilon : ¬ is_CS ({[]} : Language T) :=
  not_CS_of_nil_mem (Set.mem_singleton [])

private theorem singleton_rightQuotient_self (a : T) :
    Language.rightQuotient ({[a]} : Language T) ({[a]} : Language T) =
      ({[]} : Language T) := by
  ext w
  constructor
  · rintro ⟨v, hv, hwv⟩
    rw [Set.mem_singleton_iff] at hv
    subst v
    rw [Set.mem_singleton_iff] at hwv ⊢
    cases w <;> simp_all
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨[a], Set.mem_singleton [a], Set.mem_singleton [a]⟩

/-- Context-sensitive languages are not closed under right quotient. -/
public theorem CS_notClosedUnderRightQuotient [Nonempty T] :
    ¬ ClosedUnderRightQuotient (α := T) is_CS := by
  intro hclosed
  let a : T := Classical.ofNonempty
  have hq := hclosed ({[a]} : Language T) ({[a]} : Language T)
    (CS_singleton_letter a) (CS_singleton_letter a)
  rw [singleton_rightQuotient_self a] at hq
  exact not_CS_epsilon hq

/-- Context-sensitive languages are not closed under right quotient with regular languages. -/
public theorem CS_notClosedUnderRightQuotientWithRegular [Nonempty T] :
    ¬ ClosedUnderRightQuotientWithRegular (α := T) is_CS := by
  intro hclosed
  let a : T := Classical.ofNonempty
  have hq := hclosed ({[a]} : Language T) (CS_singleton_letter a)
    ({[a]} : Language T) (Language.isRegular_singleton_letter a)
  rw [singleton_rightQuotient_self a] at hq
  exact not_CS_epsilon hq
