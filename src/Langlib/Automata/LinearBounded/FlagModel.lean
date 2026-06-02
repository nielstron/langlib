module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic
@[expose]
public section

/-!
# The marker-free flag LBA model (internal)

This is an alternative LBA presentation used **internally** by the `CS = LBA` development. The
input occupies exactly `|w|` cells over the tape alphabet `Option (T ⊕ Γ)` (written canonically
via `some ∘ Sum.inl`), and the empty word is decided by an external Boolean flag `acceptEmpty` —
a bounded tape has no cell to run on for `ε`. This mirrors the optional `S → ε` rule of a
context-sensitive grammar: the flag decides membership of `ε` and is otherwise irrelevant to the
genuinely space-bounded computation on non-empty inputs.

It is proved equal to the canonical **endmarker** model `is_LBA`/`LBA`
(`Automata/LinearBounded/Definition.lean`) in `Equivalence/EndmarkerTape.lean` (flag ⊆ endmarker)
and `Equivalence/EndmarkerToFlag.lean` (endmarker ⊆ flag), so the two are interchangeable.
-/

namespace LBA

/-- Recognition with an explicit decision for the empty word.

The bounded tape requires at least one cell, so this LBA cannot run on the empty input the way a
Turing machine can. We therefore pair the machine with a Boolean `acceptEmpty` that decides
membership of `ε` directly. On non-empty words this coincides with `LanguageViaEmbed`. -/
@[expose]
public noncomputable def LanguageRecognized {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) (acceptEmpty : Bool) : Language T :=
  fun w => (acceptEmpty = true ∧ w = []) ∨ LanguageViaEmbed M embed w

end LBA

/-- A language over a finite alphabet `T` is **flag-LBA**-recognizable if it is accepted by some
finite nondeterministic LBA over the tape alphabet `Option (T ⊕ Γ)` (for an arbitrary finite work
alphabet `Γ`), with the input written canonically via `some ∘ Sum.inl`, together with an explicit
`acceptEmpty` decision for the empty word.

This is the internal intermediary for `CS = LBA`; it equals the canonical endmarker class
`is_LBA` (see `Equivalence/EndmarkerToFlag.lean`'s `LBA_eq_LBA_flag`). -/
@[expose]
public def is_LBA_flag {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (acceptEmpty : Bool)
    (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
    LBA.LanguageRecognized M (fun t => some (Sum.inl t)) acceptEmpty = L

@[expose]
public def LBA_flag {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_LBA_flag
