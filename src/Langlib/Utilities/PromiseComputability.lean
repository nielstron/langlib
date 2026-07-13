module

public import Mathlib.Computability.Halting
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
`ComputablePredOnPromise valid p` existentially packages such an evaluator for a
unary predicate.

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

/-- A predicate is computable on the promised inputs when one partial-recursive
Boolean evaluator is total and correct at every input satisfying `valid`.

Unlike `ComputablePred`, the evaluator may diverge away from the promise.  This is
essential for semantic promises such as "this program halts on every word": the raw
program syntax is effectively encoded even though validity itself is undecidable. -/
@[expose]
public def ComputablePredOnPromise [Primcodable Code]
    (valid : Code → Prop) (predicate : Code → Prop) : Prop :=
  ∃ eval : Code →. Bool, Partrec eval ∧
    ∀ c, valid c → (eval c).Dom ∧ (predicate c ↔ true ∈ eval c)

/-- An ordinary computable predicate is computable under any promise. -/
public theorem ComputablePredOnPromise.ofComputablePred
    [Primcodable Code] {valid predicate : Code → Prop}
    (h : ComputablePred predicate) :
    ComputablePredOnPromise valid predicate := by
  obtain ⟨f, hf, hspec⟩ := ComputablePred.computable_iff.mp h
  refine ⟨fun c ↦ Part.some (f c), hf.partrec, ?_⟩
  intro c _
  refine ⟨Part.some_dom _, ?_⟩
  have hc := congrFun hspec c
  simpa using iff_of_eq hc

/-- If every input satisfies the promise, promise computability is ordinary
`ComputablePred` computability. -/
public theorem ComputablePredOnPromise.toComputablePred
    [Primcodable Code] {valid predicate : Code → Prop}
    (h : ComputablePredOnPromise valid predicate)
    (hall : ∀ c, valid c) : ComputablePred predicate := by
  obtain ⟨eval, heval, hspec⟩ := h
  have hdom (c : Code) : (eval c).Dom := (hspec c (hall c)).1
  let decide : Code → Bool := fun c ↦ (eval c).get (hdom c)
  have hdecide : Computable decide :=
    heval.of_eq_tot fun c ↦ Part.get_mem (hdom c)
  apply ComputablePred.computable_iff.mpr
  refine ⟨decide, hdecide, ?_⟩
  funext c
  apply propext
  rw [(hspec c (hall c)).2]
  constructor
  · intro htrue
    exact Part.mem_unique (Part.get_mem (hdom c)) htrue
  · intro htrue
    rw [← htrue]
    exact Part.get_mem (hdom c)

/-- With the trivial promise, `ComputablePredOnPromise` is exactly
`ComputablePred`. -/
public theorem computablePredOnPromise_true_iff
    [Primcodable Code] (predicate : Code → Prop) :
    ComputablePredOnPromise (fun _ : Code ↦ True) predicate ↔
      ComputablePred predicate := by
  constructor
  · intro h
    exact h.toComputablePred fun _ ↦ trivial
  · exact ComputablePredOnPromise.ofComputablePred

/-- Acceptance by a partial-recursive Boolean evaluator is recursively enumerable:
run the evaluator, return when it says `true`, and diverge when it says `false`. -/
public theorem Partrec.true_mem_re [Primcodable Code]
    {eval : Code →. Bool} (heval : Partrec eval) :
    REPred (fun c ↦ true ∈ eval c) := by
  let accept : Code →. Unit := fun c ↦
    (eval c).bind fun b ↦ _root_.cond b (Part.some ()) Part.none
  have hbranch : Partrec₂ (fun (_ : Code) (b : Bool) ↦
      _root_.cond b (Part.some ()) Part.none) := by
    have h : Partrec (fun p : Code × Bool ↦
        _root_.cond p.2 (Part.some ()) Part.none) :=
      Partrec.cond Computable.snd (Partrec.const' (Part.some ())) Partrec.none
    exact h.to₂
  have haccept : Partrec accept := heval.bind hbranch
  exact haccept.dom_re.of_eq fun c ↦ by
    simp [accept, Part.dom_iff_mem]

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
