module

public import Mathlib.Computability.PartrecCode

@[expose]
public section

/-!
# Computability under a semantic promise

An effective presentation is sometimes most naturally described by a raw,
computably encoded type of programs together with a *semantic* validity promise.
For example, a raw partial-recursive program is a valid decider when it halts on
every input.  Validity need not itself be decidable: the algorithm is required to
halt only when its code satisfies the promise.

`ComputableOnPromise valid eval` says that `eval` is one uniform partial-recursive
evaluator and is total on every valid code.  `DecidesOnPromise` additionally says
that its Boolean result decides a relation on the promised inputs.

These predicates deliberately retain the raw `Primcodable` code type.  Replacing it
by the subtype `{c // valid c}` would incorrectly require a computable encoding of a
generally undecidable semantic property.
-/

variable {Code Input Output : Type}

/-- A uniform partial-recursive evaluator which is guaranteed to return on every
input whenever its raw code satisfies `valid`.  No effectiveness assumption is
made about the semantic promise itself. -/
@[expose]
public def ComputableOnPromise
    [Primcodable Code] [Primcodable Input] [Primcodable Output]
    (valid : Code → Prop) (eval : Code → Input →. Output) : Prop :=
  Partrec₂ eval ∧ ∀ c, valid c → ∀ x, (eval c x).Dom

/-- A uniform partial-recursive Boolean evaluator which, on valid codes, always
returns and returns `true` exactly when `relation c x` holds. -/
@[expose]
public def DecidesOnPromise
    [Primcodable Code] [Primcodable Input]
    (valid : Code → Prop) (eval : Code → Input →. Bool)
    (relation : Code → Input → Prop) : Prop :=
  ComputableOnPromise valid eval ∧
    ∀ c, valid c → ∀ x, relation c x ↔ true ∈ eval c x

/-- The totality component available from a promise decider. -/
public theorem DecidesOnPromise.total
    [Primcodable Code] [Primcodable Input]
    {valid : Code → Prop} {eval : Code → Input →. Bool}
    {relation : Code → Input → Prop}
    (h : DecidesOnPromise valid eval relation) {c : Code} (hc : valid c) (x : Input) :
    (eval c x).Dom :=
  h.1.2 c hc x

/-- The correctness component available from a promise decider. -/
public theorem DecidesOnPromise.correct
    [Primcodable Code] [Primcodable Input]
    {valid : Code → Prop} {eval : Code → Input →. Bool}
    {relation : Code → Input → Prop}
    (h : DecidesOnPromise valid eval relation) {c : Code} (hc : valid c) (x : Input) :
    relation c x ↔ true ∈ eval c x :=
  h.2 c hc x
