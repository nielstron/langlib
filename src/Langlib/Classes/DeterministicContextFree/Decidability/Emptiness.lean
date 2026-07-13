module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.ContextFree.Decidability.Emptiness
public import Langlib.Classes.DeterministicContextFree.Decidability.Membership
@[expose]
public section


/-! # Computability of Emptiness for Deterministic Context-Free Languages

We use the same presentation as DCFL membership: a raw `EncodedCFG`, under the
semantic promise that its language is deterministic context-free.  CFG emptiness
is uniformly decidable on every raw code, so in particular it is decidable on
the promised DCFL codes.

This argument is specific to emptiness.  It does not turn semantic closure under
complement into an effective construction on this presentation: a valid code is
not accompanied by an encoded deterministic automaton.
-/

variable {T : Type} [Fintype T] [DecidableEq T] [Primcodable T]

namespace DCFEncodedCFG

/-- **DCFL emptiness is uniformly computable from a valid encoded CFG.**

Valid codes present exactly the deterministic context-free languages, raw CFG
membership is semidecidable, and the CFG emptiness checker works on every raw
encoded grammar. -/
public theorem dcf_computableEmptiness :
    ComputableEmptiness DCF (contextFreeLanguageOf : EncodedCFG T → Language T)
      (valid := Valid) := by
  refine ⟨?_, contextFree_membership_computablePred.to_re, ?_⟩
  · intro L
    exact (exists_valid_iff_is_DCF L).symm
  · exact ComputablePredOnPromise.ofComputablePred
      contextFree_emptiness_computablePred

end DCFEncodedCFG

end
