module

public import Langlib.Classes.Recursive.Decidability.Membership

@[expose]
public section

/-!
# Effective compilation of total Boolean families

This file packages the parameter theorem (`s-m-n`) for the promised presentation
of recursive languages.  A Boolean predicate `test a w` which is computable jointly
in a parameter `a` and a word `w` can be compiled into a raw partial-recursive code.
The compiler is itself computable in `a`, and every code it produces satisfies the
semantic `RecursiveDeciderCode.Valid` promise.

The construction is useful for reductions to semantic questions about recursive
languages: it ensures that a reduction never queries the putative algorithm on an
invalid (non-total) code.
-/

namespace RecursiveDeciderCode

open Encodable

variable {A T : Type} [Primcodable A] [Primcodable T]

/-- The unary partial function which evaluates a jointly computable Boolean family
after decoding its parameter/word pair. -/
@[expose]
public def compileBoolJoint (test : A → List T → Bool) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := A × List T) n) fun (p : A × List T) =>
    Part.some (encode (test p.1 p.2))

public theorem compileBoolJoint_partrec
    (test : A → List T → Bool) (htest : Computable₂ test) :
    Nat.Partrec (compileBoolJoint test) := by
  exact htest

/-- A fixed code for the joint evaluator underlying `compileBool`. -/
@[expose]
public noncomputable def compileBoolBase
    (test : A → List T → Bool) (htest : Computable₂ test) :
    Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (compileBoolJoint_partrec test htest))

public theorem compileBoolBase_spec
    (test : A → List T → Bool) (htest : Computable₂ test) :
    (compileBoolBase test htest).eval = compileBoolJoint test :=
  Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (compileBoolJoint_partrec test htest))

/-- Compile a parameterized total Boolean predicate into a raw decider code.

Although a base universal program is chosen noncomputably once, specialization in
the parameter is the computable syntactic `Code.curry` operation. -/
@[expose]
public noncomputable def compileBool
    (test : A → List T → Bool) (htest : Computable₂ test) :
    A → Nat.Partrec.Code :=
  fun a => Nat.Partrec.Code.curry (compileBoolBase test htest) (encode a)

/-- Specializing the joint program is computable in the parameter. -/
public theorem compileBool_computable
    (test : A → List T → Bool) (htest : Computable₂ test) :
    Computable (compileBool test htest) := by
  exact (Nat.Partrec.Code.primrec₂_curry.comp
    (_root_.Primrec.const (compileBoolBase test htest)) Primrec.encode).to_comp

/-- The compiled raw program returns the encoded Boolean result. -/
public theorem compileBool_eval
    (test : A → List T → Bool) (htest : Computable₂ test)
    (a : A) (w : List T) :
    (compileBool test htest a).eval (encode w) =
      Part.some (encode (test a w)) := by
  rw [compileBool, Nat.Partrec.Code.eval_curry, compileBoolBase_spec]
  simp [compileBoolJoint]

/-- `evalBool` of a compiled code is exactly the original total Boolean test. -/
public theorem evalBool_compileBool
    (test : A → List T → Bool) (htest : Computable₂ test)
    (a : A) (w : List T) :
    evalBool (compileBool test htest a) w = Part.some (test a w) := by
  rw [evalBool, compileBool_eval]
  cases test a w <;> rfl

/-- Every code produced by `compileBool` satisfies the always-halting promise. -/
public theorem compileBool_valid
    (test : A → List T → Bool) (htest : Computable₂ test) (a : A) :
    Valid (T := T) (compileBool test htest a) := by
  intro w
  rw [evalBool_compileBool]
  simp

/-- Membership in a compiled language is the source Boolean test. -/
public theorem mem_language_compileBool_iff
    (test : A → List T → Bool) (htest : Computable₂ test)
    (a : A) (w : List T) :
    w ∈ language (T := T) (compileBool test htest a) ↔ test a w = true := by
  change true ∈ evalBool (compileBool test htest a) w ↔ _
  rw [evalBool_compileBool]
  exact Part.mem_some_iff.trans eq_comm

/-- The language of a compiled code is the language selected by the Boolean test. -/
public theorem language_compileBool
    (test : A → List T → Bool) (htest : Computable₂ test) (a : A) :
    language (T := T) (compileBool test htest a) =
      {w | test a w = true} := by
  ext w
  exact mem_language_compileBool_iff test htest a w

end RecursiveDeciderCode
