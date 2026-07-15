module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Automata.FiniteState.Inclusion.DeterministicPushdown
public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Examples.AnBn
public import Langlib.Classes.Regular.Examples.AnBn

@[expose]
public section

/-! # Finite Automata Strictly Included in Deterministic Pushdown Automata

The proof is entirely at the automata level.  Inclusion is the explicit
stack-ignoring simulation `DPDA_of_DFA` (preceded by subset determinization for
NFAs).  Strictness is witnessed by the explicit DPDA `dpda_anbn`, whose language
`{aⁿbⁿ}` is not accepted by any DFA.  Injective input relabelling transports
that witness from `Bool` to every finite alphabet containing at least two
symbols.

## Main results

- `DFA_strict_subclass_DPDA` — `DFA.Class ⊂ DPDA.Class` on every nontrivial
  finite alphabet.
- `NFA_strict_subclass_DPDA` — `NFA.Class ⊂ DPDA.Class` under the same
  assumptions.
- `_of_embedding` and `_of_card` variants state the exact alphabet requirement.
-/

open Classical

noncomputable section

variable {T : Type} [Fintype T]

/-- Relabelling the explicit `{aⁿbⁿ}` DPDA along an alphabet embedding gives
a DPDA for the relabelled language. -/
public theorem map_anbn_is_DPDA (e : Bool ↪ T) :
    is_DPDA (Language.map e anbn) := by
  let M : DPDA (Fin 4) T Bool :=
    DPDA.mapInput dpda_anbn e (Function.invFun e)
  refine ⟨Fin 4, Bool, inferInstance, inferInstance, M, ?_⟩
  dsimp [M]
  rw [DPDA.map_acceptsByFinalState_of_injective e.injective, dpda_anbn_accepts]

/-- DFA languages are strictly contained in DPDA languages whenever `Bool`
embeds in the alphabet. -/
public theorem DFA_strict_subclass_DPDA_of_embedding (e : Bool ↪ T) :
    (DFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  refine ⟨DFA_subclass_DPDA, ?_⟩
  intro hDPDA_DFA
  have hregular : (Language.map e anbn).IsRegular :=
    hDPDA_DFA (map_anbn_is_DPDA e)
  exact map_anbn_not_isRegular e.injective hregular

/-- DFA languages are strictly contained in DPDA languages over every finite
alphabet with at least two symbols. -/
public theorem DFA_strict_subclass_DPDA_of_card
    (hT : 2 ≤ Fintype.card T) :
    (DFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide) hT)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (by simpa using hT :
    Fintype.card Bool ≤ Fintype.card T)
  exact DFA_strict_subclass_DPDA_of_embedding e

/-- DFA languages are strictly contained in DPDA languages over every
nontrivial finite alphabet. -/
public theorem DFA_strict_subclass_DPDA [Nontrivial T] :
    (DFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  exact DFA_strict_subclass_DPDA_of_card (by exact Fintype.one_lt_card)

/-- NFA languages are strictly contained in DPDA languages whenever `Bool`
embeds in the alphabet.  Nonmembership of the witness is shown by explicitly
determinizing any hypothetical accepting NFA. -/
public theorem NFA_strict_subclass_DPDA_of_embedding (e : Bool ↪ T) :
    (NFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  refine ⟨NFA_subclass_DPDA, ?_⟩
  intro hDPDA_NFA
  obtain ⟨Q, hQ, M, hM⟩ := hDPDA_NFA (map_anbn_is_DPDA e)
  have hregular : (Language.map e anbn).IsRegular :=
    ⟨Set Q, inferInstance, M.toDFA, NFA.toDFA_correct.trans hM⟩
  exact map_anbn_not_isRegular e.injective hregular

/-- NFA languages are strictly contained in DPDA languages over every finite
alphabet with at least two symbols. -/
public theorem NFA_strict_subclass_DPDA_of_card
    (hT : 2 ≤ Fintype.card T) :
    (NFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide) hT)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (by simpa using hT :
    Fintype.card Bool ≤ Fintype.card T)
  exact NFA_strict_subclass_DPDA_of_embedding e

/-- NFA languages are strictly contained in DPDA languages over every
nontrivial finite alphabet. -/
public theorem NFA_strict_subclass_DPDA [Nontrivial T] :
    (NFA.Class : Set (Language T)) ⊂ DPDA.Class := by
  exact NFA_strict_subclass_DPDA_of_card (by exact Fintype.one_lt_card)

end
