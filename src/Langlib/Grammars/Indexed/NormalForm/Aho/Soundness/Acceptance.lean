module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Certificates

@[expose]
public section

/-!
# Accepting-run soundness for Aho's machine

The forward derivation invariant and the final theorem from accepting machine runs to grammar
generation.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace ControlDenotation

open BlockDenotation

/-! ## Forward derivation invariant and accepting-run soundness -/

/-- The consumed input prefix followed by the execution-ordered remaining form is derivable from
the grammar start symbol. -/
public def ForwardInvariant (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (c : Config g) : Prop :=
  ∃ form,
    Config.Represents c form ∧
      c.inputPos ≤ input.length ∧
      g.Derives [ISym.indexed g.initial []]
        ((input.take c.inputPos).map ISym.terminal ++ form)

public theorem initial_forwardInvariant
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T) :
    ForwardInvariant g input (initialConfig g) := by
  refine ⟨[ISym.indexed g.initial []], initialConfig_represents g, by simp [initialConfig], ?_⟩
  simpa [initialConfig] using
    (deri_self g [ISym.indexed g.initial []])

public theorem compositeStep_preserves_represents
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} {form : List g.ISym}
    (hstep : CompositeStep g input c c')
    (hrep : Config.Represents c form) :
    ∃ form', Config.Represents c' form' ∧ StepEffect g input c c' form form' := by
  rcases hstep with ⟨cert, hcert⟩
  exact certStep_preserves_represents input cert hcert hrep

public theorem compositeStep_preserves_forwardInvariant
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} (hstep : CompositeStep g input c c')
    (hinv : ForwardInvariant g input c) : ForwardInvariant g input c' := by
  rcases hinv with ⟨form, hrep, hpos, hderiv⟩
  rcases compositeStep_preserves_represents input hstep hrep with
    ⟨form', hrep', heffect⟩
  rcases heffect with ⟨hposEq, hgrammar⟩ | ⟨a, hform, hinput, hposEq⟩
  · refine ⟨form', hrep', ?_, ?_⟩
    · rw [hposEq]
      exact hpos
    · rw [hposEq]
      exact hderiv.trans
        (deri_with_prefix ((input.take c.inputPos).map ISym.terminal) hgrammar)
  · have hlt : c.inputPos < input.length :=
      (List.getElem?_eq_some_iff.mp hinput).choose
    refine ⟨form', hrep', ?_, ?_⟩
    · rw [hposEq]
      exact Nat.succ_le_of_lt hlt
    · rw [hposEq]
      rw [hform] at hderiv
      simpa [List.take_add_one, hinput, List.map_append, List.append_assoc] using hderiv

public theorem reachable_forwardInvariant
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c : Config g}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c) :
    ForwardInvariant g input c := by
  induction hreach with
  | refl => exact initial_forwardInvariant g input
  | tail _ hstep ih =>
      exact compositeStep_preserves_forwardInvariant input hstep ih

public theorem finalConfig_represents_only_nil
    (g : IndexedGrammar T) [Fintype g.nt] (n : ℕ) {form : List g.ISym}
    (hrep : Config.Represents (finalConfig g n) form) : form = [] := by
  change ExecRep g ⟨[WorkSym.dollar], WorkSym.hash, []⟩ form at hrep
  have hash_form_nil : ∀ {cursor : WorkCursor g} {w : List g.ISym},
      ExecRep g cursor w → cursor.focus = WorkSym.hash → w = [] := by
    intro cursor w h
    induction h <;> simp_all
  exact hash_form_nil hrep rfl

/-- Every accepting run of the composite machine spells a genuine indexed-grammar derivation. -/
public theorem ahoMachine_sound
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (hreach : Relation.ReflTransGen (CompositeStep g input)
      (initialConfig g) (finalConfig g input.length)) :
    g.Generates input := by
  rcases reachable_forwardInvariant input hreach with
    ⟨form, hrep, _hpos, hderiv⟩
  have hform : form = [] := finalConfig_represents_only_nil g input.length hrep
  subst form
  simpa [Generates, finalConfig] using hderiv

end ControlDenotation
end Aho
end IndexedGrammar
