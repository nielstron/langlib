module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolStepCorrectness
import Mathlib.Tactic

@[expose]
public section

/-!
# Correctness of certified-row inductive counting

This is the machine-independent, space-bounded form of the
Immerman--Szelepcsényi theorem.  The protocol in `Construction.lean` streams canonical
enumerations and bounded path witnesses; no complete reachable set is stored in a row.

The construction follows:

* Neil Immerman, *Nondeterministic space is closed under complementation* (1988).
* Róbert Szelepcsényi, *The method of forced enumeration for nondeterministic automata*
  (1988).

Context-sensitive closure under complement is only a downstream corollary obtained by
presenting an LBA computation graph as a certified row system.
-/

open Classical

namespace CertifiedRowSystem
namespace Complement

variable {I A C Q F : Type*}

/-- The source system has no reachable final row from this concrete input row. -/
public def SourceRejects (S : CertifiedRowSystem I A C Q F) (input : List I) : Prop :=
  ¬ ∃ row,
    Relation.ReflTransGen S.RowStep (input.map S.inputCell) row ∧ S.Final row

/-- Rejection is exactly nonmembership on a nonempty input. -/
public theorem sourceRejects_iff_not_mem
    (S : CertifiedRowSystem I A C Q F) {input : List I} (hne : input ≠ []) :
    SourceRejects S input ↔ input ∉ S.rowReachLanguage := by
  constructor
  · intro hrejected hmem
    exact hrejected hmem.2
  · intro hnotMem hreach
    exact hnotMem ⟨hne, hreach⟩

/-- The integrated protocol reaches a uniformly accepting row. -/
public def ProtocolAccepts
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) : Prop :=
  ∃ row,
    Relation.ReflTransGen (ProtocolStep D)
      (input.map (inputProtocolCell D.inputCell)) row ∧
      HasPhase .accept row

/-- Reachability in the compiled protocol system, stated before replacing its certified
row relation by the semantic union `ProtocolStep`. -/
public def CompiledProtocolAccepts
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) : Prop :=
  ∃ row,
    Relation.ReflTransGen (deterministicComplementSystem D).RowStep
      (input.map (inputProtocolCell D.inputCell)) row ∧
      HasPhase .accept row

/-- Membership in the constructed row language is compiled protocol acceptance together
with the model's intrinsic nonempty-input condition. -/
public theorem mem_deterministicComplementSystem_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    input ∈ (deterministicComplementSystem D).rowReachLanguage ↔
      input ≠ [] ∧ CompiledProtocolAccepts D input := by
  constructor
  · rintro ⟨hne, row, hreach, hfinal⟩
    exact ⟨hne, row, hreach, (final_deterministicComplementSystem_iff D row).1 hfinal⟩
  · rintro ⟨hne, row, hreach, hfinal⟩
    exact ⟨hne, row, hreach, (final_deterministicComplementSystem_iff D row).2 hfinal⟩

end Complement
end CertifiedRowSystem
