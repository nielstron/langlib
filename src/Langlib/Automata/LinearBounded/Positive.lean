module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic
@[expose]
public section

/-!
# The bounded-tape LBA model (ε-free)

This is the marker-free `|w|`-cell LBA model, used **internally** as the genuinely space-bounded
core of the `CS = LBA` development. The input occupies exactly `|w|` cells over the tape alphabet
`Option (T ⊕ Γ)` (written canonically via `some ∘ Sum.inl`); the working space comes entirely from
the arbitrary finite work alphabet `Γ`.

A bounded tape has no cell to run on for the empty input, so this model **cannot accept `ε`** — it
recognizes exactly the *ε-free* context-sensitive languages
(`is_LBA_pos_iff : is_LBA_pos L ↔ is_CS L ∧ [] ∉ L`, proved in
`Equivalence/ContextSensitive.lean`). The empty word is supplied separately by the canonical
**endmarker** model `is_LBA`/`LBA` (`Automata/LinearBounded/Definition.lean`), which runs on `⊢⊣`;
that is what makes the endmarker class equal to *all* of `CS` (`CS = LBA`). So no empty-word flag is
needed anywhere.
-/

/-- A language over a finite alphabet `T` is **`LBA_pos`**-recognizable if it is accepted by some
finite nondeterministic LBA over the tape alphabet `Option (T ⊕ Γ)` (for an arbitrary finite work
alphabet `Γ`), with the input written canonically via `some ∘ Sum.inl`, on a tape of exactly `|w|`
cells. Such a machine never runs on the empty input, so `[] ∉ L`; these are exactly the ε-free
context-sensitive languages (`is_LBA_pos_iff`). -/
@[expose]
public def is_LBA_pos {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
    LBA.LanguageViaEmbed M (fun t => some (Sum.inl t)) = L

@[expose]
public def LBA_pos {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_LBA_pos
