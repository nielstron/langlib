import Langlib.Automata.Turing.DSL.DirectBridge

/-! # Legacy Encoding Bridge Compatibility

The old `EncodingBridge` module has been replaced by `DirectBridge`.  The
public theorem name `code_implies_isTM` is kept here as an alias for the new
direct proof, so existing imports can migrate gradually.
-/

open Turing

theorem code_implies_isTM
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T)
    (c : Turing.ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L :=
  code_implies_isTM_direct L c hL
