module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Reachability

@[expose]
public section

/-!
# Input-head safety for Aho's machine

Every certified composite transition preserves the invariant that the input position remains
within the supplied input.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Input-head safety -/

/-- The input cursor has not moved beyond the fixed input word. -/
public def Config.InputWithin {g : IndexedGrammar T} (input : List T) (c : Config g) : Prop :=
  c.inputPos ≤ input.length

public theorem initialConfig_inputWithin (g : IndexedGrammar T) (input : List T) :
    (initialConfig g).InputWithin input := by
  simp [Config.InputWithin, initialConfig]

/-- Every certified move preserves input-head safety.  The sole advancing move carries a
successful `getElem?` check, which proves that the old cursor is strictly inside the input. -/
public theorem certStep_preserves_inputWithin
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) {c c' : Config g}
    (hstep : CertStep g input cert c c') (hin : c.InputWithin input) :
    c'.InputWithin input := by
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainTerminal A a =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainPushSkip A B f =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainPushUse A B f =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryRight A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | livePushFresh A B f =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | livePushCompress A B f R d =>
      rcases hstep with ⟨_, _, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | popPlain R d A B =>
      rcases hstep with ⟨_, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
  | popLive R d A B =>
      rcases hstep with ⟨_, _, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
  | matchTerminal a =>
      rcases hstep with ⟨hinput, alpha, Z, beta, hc, hc'⟩
      have hlt : c.inputPos < input.length :=
        (List.getElem?_eq_some_iff.mp hinput).choose
      rw [hc']
      simp only [Config.InputWithin]
      omega
  | eraseIndex R d =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, _, _, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin

public theorem compositeStep_preserves_inputWithin
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} (hstep : CompositeStep g input c c')
    (hin : c.InputWithin input) : c'.InputWithin input := by
  rcases hstep with ⟨cert, hcert⟩
  exact certStep_preserves_inputWithin input cert hcert hin

end Aho
end IndexedGrammar

