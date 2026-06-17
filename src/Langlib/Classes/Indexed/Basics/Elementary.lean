module

public import Langlib.Classes.Indexed.Definition
@[expose]
public section

/-! # Elementary indexed languages

This file provides small indexed-grammar witnesses used by structural reductions.
-/

namespace IndexedGrammar

variable {T : Type}

/-- The indexed grammar with one nonterminal, one flag symbol, and no rules. -/
public def emptyGrammar (T : Type) : IndexedGrammar T where
  nt := PUnit
  flag := PUnit
  initial := PUnit.unit
  rules := []

public instance emptyGrammar_nt_decidableEq (T : Type) :
    DecidableEq (emptyGrammar T).nt := by
  change DecidableEq PUnit
  infer_instance

public instance emptyGrammar_nt_fintype (T : Type) :
    Fintype (emptyGrammar T).nt := by
  change Fintype PUnit
  infer_instance

public instance emptyGrammar_flag_fintype (T : Type) :
    Fintype (emptyGrammar T).flag := by
  change Fintype PUnit
  infer_instance

public theorem emptyGrammar_noEpsilon (T : Type) :
    (emptyGrammar T).NoEpsilon' := by
  intro r hr
  simp [emptyGrammar] at hr

public theorem emptyGrammar_isNormalForm (T : Type) :
    (emptyGrammar T).IsNormalForm := by
  intro r hr
  simp [emptyGrammar] at hr

/-- The no-rule indexed grammar generates the empty language. -/
public theorem emptyGrammar_language (T : Type) :
    (emptyGrammar T).Language = (0 : _root_.Language T) := by
  ext w
  constructor
  · intro hw
    change (emptyGrammar T).Derives [ISym.indexed PUnit.unit []] (w.map ISym.terminal) at hw
    rcases Relation.ReflTransGen.cases_tail hw with hEq | ⟨_, _, hstep⟩
    · cases w with
      | nil => simp [emptyGrammar] at hEq
      | cons a rest => simp [emptyGrammar] at hEq
    · rcases hstep with ⟨r, u, v, σ, hr, _, _⟩
      simp [emptyGrammar] at hr
  · intro h
    cases h

end IndexedGrammar

variable {T : Type}

/-- The empty language is indexed. -/
public theorem is_Indexed_empty : is_Indexed (0 : Language T) :=
  ⟨IndexedGrammar.emptyGrammar T, IndexedGrammar.emptyGrammar_language T⟩

/-- The empty language has an ε-free indexed-grammar witness. -/
public theorem is_Indexed_noEpsilon_empty : is_Indexed_noEpsilon (0 : Language T) :=
  ⟨IndexedGrammar.emptyGrammar T, IndexedGrammar.emptyGrammar_noEpsilon T,
    IndexedGrammar.emptyGrammar_language T⟩
