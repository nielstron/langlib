module

public import Langlib.Classes.ContextSensitive.Closure.Union
public import Langlib.Classes.ContextSensitive.Examples.SingletonWord
import Mathlib.Tactic
@[expose]
public section

/-! # Finite context-sensitive languages

Every finite language is context-sensitive. The proof uses an explicit empty grammar for the
empty language, singleton-word context-sensitivity, and binary union closure.
-/

variable {T : Type}

/-- The empty language is context-sensitive. -/
public theorem emptyLanguage_is_CS (T : Type) : is_CS (⊥ : Language T) := by
  classical
  let g : grammar T := { nt := Unit, initial := (), rules := [] }
  refine ⟨g, grammar_context_sensitive_of_noncontracting g ?_, ?_⟩
  · intro r hr
    simp [g] at hr
  · ext w
    constructor
    · intro hw
      change grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) at hw
      rw [grammar_derives_iff_exists_derivesIn] at hw
      rcases hw with ⟨n, hn⟩
      induction n generalizing w with
      | zero =>
          cases w <;> simp [g] at hn
      | succ n ih =>
          rw [grammar_derivesIn_succ] at hn
          rcases hn with ⟨mid, _hprev, hstep⟩
          rcases hstep with ⟨r, hr, _⟩
          simp [g] at hr
    · intro hw
      exact False.elim hw

/-- The language represented by a finite set of words is context-sensitive. -/
public theorem finsetLanguage_is_CS [Fintype T] (s : Finset (List T)) :
    is_CS (fun w : List T => w ∈ s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using emptyLanguage_is_CS T
  | insert w s hnot ih =>
      let Lw : Language T := fun u : List T => u = w
      let Ls : Language T := fun u : List T => u ∈ s
      have hsingle : is_CS Lw := by
        simpa [Lw, singletonWordLanguage] using singletonWordLanguage_is_CS (T := T) w
      have hs : is_CS Ls := by
        simpa [Ls] using ih
      have hunion : is_CS (Lw + Ls) :=
        CS_closedUnderUnion Lw Ls hsingle hs
      convert hunion using 1
      ext u
      simp only [Finset.mem_insert]
      change (u = w ∨ u ∈ s) ↔ (u = w ∨ u ∈ s)
      rfl

/-- Every finite language over a finite alphabet is context-sensitive. -/
public theorem is_CS_of_finite_language [Fintype T] {L : Language T}
    (hfin : (L : Set (List T)).Finite) :
    is_CS L := by
  classical
  let s : Finset (List T) := Set.Finite.toFinset hfin
  have hs : (fun w : List T => w ∈ s) = L := by
    ext w
    simp [s, Set.Finite.mem_toFinset]
    rfl
  simpa [hs] using finsetLanguage_is_CS (T := T) s

end
