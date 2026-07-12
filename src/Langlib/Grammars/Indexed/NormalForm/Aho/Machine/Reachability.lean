module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Transitions

@[expose]
public section

/-!
# Bounded reachability for Aho's machine

Logical work-width bounds carried across finite composite-machine runs.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Reachability with an invariant on every intermediate configuration -/

/-- The logical work word of a configuration fits in `bound` squares. -/
public def Config.Within {g : IndexedGrammar T} (bound : ℕ) (c : Config g) : Prop :=
  c.work.word.length ≤ bound

/-- Composite reachability whose initial configuration and both endpoints of every traversed
edge satisfy the work-tape bound.  Consequently every intermediate configuration is bounded. -/
public def BoundedReaches (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (bound : ℕ) (c c' : Config g) : Prop :=
  c.Within bound ∧
    Relation.ReflTransGen
      (fun x y => CompositeStep g input x y ∧ x.Within bound ∧ y.Within bound) c c'

namespace BoundedReaches

public theorem refl {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c : Config g} (hc : c.Within bound) :
    BoundedReaches g input bound c c :=
  ⟨hc, Relation.ReflTransGen.refl⟩

public theorem single {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c c' : Config g} (hc : c.Within bound)
    (hstep : CompositeStep g input c c') (hc' : c'.Within bound) :
    BoundedReaches g input bound c c' :=
  ⟨hc, Relation.ReflTransGen.single ⟨hstep, hc, hc'⟩⟩

public theorem trans {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c₁ c₂ c₃ : Config g}
    (h₁₂ : BoundedReaches g input bound c₁ c₂)
    (h₂₃ : BoundedReaches g input bound c₂ c₃) :
    BoundedReaches g input bound c₁ c₃ :=
  ⟨h₁₂.1, h₁₂.2.trans h₂₃.2⟩

/-- Forget the invariant and retain ordinary composite reachability. -/
public theorem toReflTransGen {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c c' : Config g}
    (h : BoundedReaches g input bound c c') :
    Relation.ReflTransGen (CompositeStep g input) c c' := by
  exact h.2.mono (fun _ _ hstep => hstep.1)

/-- Increase the available work bound. -/
public theorem mono {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {small large : ℕ} (hsl : small ≤ large) {c c' : Config g}
    (h : BoundedReaches g input small c c') :
    BoundedReaches g input large c c' := by
  refine ⟨le_trans h.1 hsl, ?_⟩
  exact h.2.mono (fun _ _ hstep =>
    ⟨hstep.1, le_trans hstep.2.1 hsl, le_trans hstep.2.2 hsl⟩)

end BoundedReaches

end Aho
end IndexedGrammar
