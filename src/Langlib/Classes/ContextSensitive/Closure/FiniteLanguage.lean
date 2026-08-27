module

public import Langlib.Classes.ContextSensitive.Closure.Union
public import Langlib.Classes.ContextSensitive.Examples.SingletonWord
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
      rcases Relation.ReflTransGen.cases_tail hw with heq | ⟨_mid, _hprev, hstep⟩
      · cases w <;> simp [g] at heq
      · rcases hstep with ⟨r, hr, _⟩
        simp [g] at hr
    · intro hw
      exact False.elim hw

/-- The language represented by a finite set of words is context-sensitive. -/
public theorem finsetLanguage_is_CS [Fintype T] (s : Finset (List T)) :
    is_CS (fun w : List T => w ∈ s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hempty :
          (fun w : List T => w ∈ (∅ : Finset (List T))) = (⊥ : Language T) := by
        rw [bot_eq_zero]
        apply Language.ext
        intro w
        constructor
        · intro hw
          exact (Finset.notMem_empty w hw).elim
        · intro hw
          exact (Language.notMem_zero w hw).elim
      rw [hempty]
      exact emptyLanguage_is_CS T
  | insert w s hnot ih =>
      let Lw : Language T := fun u : List T => u = w
      let Ls : Language T := fun u : List T => u ∈ s
      have hsingle : is_CS Lw := by
        have hLw : Lw = singletonWordLanguage w := by
          change ({u : List T | u = w} : Set (List T)) = {w}
          rfl
        rw [hLw]
        exact singletonWordLanguage_is_CS (T := T) w
      have hs : is_CS Ls := by
        simpa [Ls] using ih
      have hunion : is_CS (Lw + Ls) :=
        CS_closedUnderUnion Lw Ls hsingle hs
      have hinsert :
          (fun u : List T => u ∈ insert w s) = Lw + Ls := by
        apply Language.ext
        intro u
        simp only [Finset.mem_insert, Language.mem_add]
        change (u = w ∨ u ∈ s) ↔ (u = w ∨ u ∈ s)
        rfl
      rw [hinsert]
      exact hunion

/-- Every finite language over a finite alphabet is context-sensitive. -/
public theorem is_CS_of_finite_language [Fintype T] {L : Language T}
    (hfin : (L : Set (List T)).Finite) :
    is_CS L := by
  classical
  let s : Finset (List T) := Set.Finite.toFinset hfin
  have hs : (fun w : List T => w ∈ s) = L := by
    change (s : Set (List T)) = (L : Set (List T))
    exact hfin.coe_toFinset
  rw [← hs]
  exact finsetLanguage_is_CS (T := T) s

end
