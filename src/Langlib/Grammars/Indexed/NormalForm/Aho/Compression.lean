module

public import Langlib.Grammars.Indexed.NormalForm.ParseTree

@[expose]
public section

/-!
# Aho's finite compression of index strings

This file contains the grammar-facing part of Aho's linear-space simulation of an indexed
grammar.  A stack-neutral derivation is saturated into the four normal-form rule shapes, and a
possibly long string of flags is represented by the finite binary relation it induces on
nonterminals when it is consumed.

The actual marked-derivation machine and its linear tape bound are deliberately kept separate.
The declarations here only expose finite symbols and semantic lemmas that such a machine can use.

## Reference

* A. V. Aho, "Indexed grammars -- an extension of context-free grammars", JACM 15(4),
  Section 5, 1968.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Concrete normal-form rule predicates -/

/-- A concrete binary rule `A -> B C`. -/
public def BinaryRule (g : IndexedGrammar T) (A B C : g.nt) : Prop :=
  ∃ r ∈ g.rules,
    r.lhs = A ∧ r.consume = none ∧
      r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]

/-- A concrete flag-pop rule `A f -> B`. -/
public def PopRule (g : IndexedGrammar T) (A : g.nt) (f : g.flag) (B : g.nt) : Prop :=
  ∃ r ∈ g.rules,
    r.lhs = A ∧ r.consume = some f ∧
      r.rhs = [IRhsSymbol.nonterminal B none]

/-- A concrete flag-push rule `A -> B f`. -/
public def PushRule (g : IndexedGrammar T) (A B : g.nt) (f : g.flag) : Prop :=
  ∃ r ∈ g.rules,
    r.lhs = A ∧ r.consume = none ∧
      r.rhs = [IRhsSymbol.nonterminal B (some f)]

/-- A concrete terminal rule `A -> a`. -/
public def TerminalRule (g : IndexedGrammar T) (A : g.nt) (a : T) : Prop :=
  ∃ r ∈ g.rules,
    r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a]

/-! ## Stack-neutral saturation -/

/-- `Neutral g A B` means that `A` can become `B` while starting and ending with an empty
stack and without leaving any other sentential symbols behind.  In normal form such a derivation
can only consist of balanced flag pushes and pops; the semantic definition is more convenient for
the saturation lemmas below. -/
public def Neutral (g : IndexedGrammar T) (A B : g.nt) : Prop :=
  g.Derives [ISym.indexed A []] [ISym.indexed B []]

namespace Neutral

@[refl]
public theorem refl (g : IndexedGrammar T) (A : g.nt) : Neutral g A A :=
  Relation.ReflTransGen.refl

@[trans]
public theorem trans {g : IndexedGrammar T} {A B C : g.nt}
    (hAB : Neutral g A B) (hBC : Neutral g B C) : Neutral g A C :=
  Relation.ReflTransGen.trans hAB hBC

/-- A neutral derivation is parametric in an arbitrary inherited stack suffix. -/
public theorem lift_suffix {g : IndexedGrammar T} {A B : g.nt}
    (h : Neutral g A B) (suffix : List g.flag) :
    g.Derives [ISym.indexed A suffix] [ISym.indexed B suffix] := by
  simpa [Neutral] using derives_appendStackSuffixes h suffix

end Neutral

/-! ## Aho's augmented rule predicates

Rather than materializing an equivalent augmented grammar, we use its rules as finite semantic
predicates.  Ordinary terminal, binary, and push rules are precomposed with neutral closure.  A
pop edge is saturated on both sides: a neutral prefix may expose the concrete pop, and a neutral
suffix may follow it.  The prefix saturation is essential when a balanced push/pop segment lies
between a productive event and the next inherited flag consumption.
-/

/-- An augmented terminal edge: `A =>* B -> a`, with the first part stack-neutral. -/
public def AugTerminal (g : IndexedGrammar T) (A : g.nt) (a : T) : Prop :=
  ∃ B, Neutral g A B ∧ TerminalRule g B a

/-- An augmented binary edge: `A =>* D -> B C`, with the first part stack-neutral. -/
public def AugBinary (g : IndexedGrammar T) (A B C : g.nt) : Prop :=
  ∃ D, Neutral g A D ∧ BinaryRule g D B C

/-- An augmented push edge: `A =>* C -> B f`, with the first part stack-neutral. -/
public def AugPush (g : IndexedGrammar T) (A B : g.nt) (f : g.flag) : Prop :=
  ∃ C, Neutral g A C ∧ PushRule g C B f

/-- The relation induced by consuming one augmented flag: take a neutral prefix, pop `f`, then
take a neutral suffix.  The flag argument comes first because `AugPop g f` is used as a binary
relation. -/
public def AugPop (g : IndexedGrammar T) (f : g.flag) (A B : g.nt) : Prop :=
  ∃ D C, Neutral g A D ∧ PopRule g D f C ∧ Neutral g C B

/-! ### Ordinary rules embed into the augmented predicates -/

public theorem terminalRule_aug {g : IndexedGrammar T} {A : g.nt} {a : T}
    (h : TerminalRule g A a) : AugTerminal g A a :=
  ⟨A, Neutral.refl g A, h⟩

public theorem binaryRule_aug {g : IndexedGrammar T} {A B C : g.nt}
    (h : BinaryRule g A B C) : AugBinary g A B C :=
  ⟨A, Neutral.refl g A, h⟩

public theorem pushRule_aug {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : PushRule g A B f) : AugPush g A B f :=
  ⟨A, Neutral.refl g A, h⟩

public theorem popRule_aug {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : PopRule g A f B) : AugPop g f A B :=
  ⟨A, B, Neutral.refl g A, h, Neutral.refl g B⟩

/-! ### One-rule semantic facts -/

public theorem binaryRule_transforms {g : IndexedGrammar T} {A B C : g.nt}
    (h : BinaryRule g A B C) (suffix : List g.flag) :
    g.Transforms [ISym.indexed A suffix]
      [ISym.indexed B suffix, ISym.indexed C suffix] := by
  rcases h with ⟨r, hr, hlhs, hc, hrhs⟩
  refine ⟨r, [], [], suffix, hr, ?_, ?_⟩
  · simp [hc, hlhs]
  · rw [hrhs]
    simp [IndexedGrammar.expandRhs]

public theorem popRule_transforms {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : PopRule g A f B) (suffix : List g.flag) :
    g.Transforms [ISym.indexed A (f :: suffix)] [ISym.indexed B suffix] := by
  rcases h with ⟨r, hr, hlhs, hc, hrhs⟩
  refine ⟨r, [], [], suffix, hr, ?_, ?_⟩
  · simp [hc, hlhs]
  · rw [hrhs]
    simp [IndexedGrammar.expandRhs]

public theorem pushRule_transforms {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : PushRule g A B f) (suffix : List g.flag) :
    g.Transforms [ISym.indexed A suffix] [ISym.indexed B (f :: suffix)] := by
  rcases h with ⟨r, hr, hlhs, hc, hrhs⟩
  refine ⟨r, [], [], suffix, hr, ?_, ?_⟩
  · simp [hc, hlhs]
  · rw [hrhs]
    simp [IndexedGrammar.expandRhs]

public theorem terminalRule_transforms {g : IndexedGrammar T} {A : g.nt} {a : T}
    (h : TerminalRule g A a) (suffix : List g.flag) :
    g.Transforms [ISym.indexed A suffix] [ISym.terminal a] := by
  rcases h with ⟨r, hr, hlhs, hc, hrhs⟩
  refine ⟨r, [], [], suffix, hr, ?_, ?_⟩
  · simp [hc, hlhs]
  · rw [hrhs]
    simp [IndexedGrammar.expandRhs]

/-! ### Soundness of augmented edges -/

public theorem augTerminal_derives {g : IndexedGrammar T} {A : g.nt} {a : T}
    (h : AugTerminal g A a) (suffix : List g.flag) :
    g.Derives [ISym.indexed A suffix] [ISym.terminal a] := by
  rcases h with ⟨B, hneutral, hrule⟩
  exact (Neutral.lift_suffix hneutral suffix).trans
    (deri_of_tran (terminalRule_transforms hrule suffix))

public theorem augBinary_derives {g : IndexedGrammar T} {A B C : g.nt}
    (h : AugBinary g A B C) (suffix : List g.flag) :
    g.Derives [ISym.indexed A suffix]
      [ISym.indexed B suffix, ISym.indexed C suffix] := by
  rcases h with ⟨D, hneutral, hrule⟩
  exact (Neutral.lift_suffix hneutral suffix).trans
    (deri_of_tran (binaryRule_transforms hrule suffix))

public theorem augPush_derives {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : AugPush g A B f) (suffix : List g.flag) :
    g.Derives [ISym.indexed A suffix] [ISym.indexed B (f :: suffix)] := by
  rcases h with ⟨C, hneutral, hrule⟩
  exact (Neutral.lift_suffix hneutral suffix).trans
    (deri_of_tran (pushRule_transforms hrule suffix))

public theorem augPop_derives {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    (h : AugPop g f A B) (suffix : List g.flag) :
    g.Derives [ISym.indexed A (f :: suffix)] [ISym.indexed B suffix] := by
  rcases h with ⟨D, C, hprefix, hrule, hsuffix⟩
  exact (Neutral.lift_suffix hprefix (f :: suffix)).trans
    ((deri_of_tran (popRule_transforms hrule suffix)).trans
      (Neutral.lift_suffix hsuffix suffix))

/-! ## Finite compressed flags -/

/-- A compressed flag is the Boolean adjacency matrix of the relation it induces on
nonterminals.  For a finite nonterminal type this is itself a finite type, independently of the
number or length of concrete flag strings represented by it. -/
public abbrev CFlag (g : IndexedGrammar T) : Type :=
  g.nt → g.nt → Bool

/-- The empty compressed relation. -/
public def cflagZero (g : IndexedGrammar T) : CFlag g :=
  fun _ _ => false

/-- The compressed relation denoted by one concrete flag, including Aho's neutral
post-saturation of a pop edge. -/
public noncomputable def cflagBase (g : IndexedGrammar T) (f : g.flag) : CFlag g := by
  classical
  exact fun A B => decide (AugPop g f A B)

/-- Relational composition of two compressed flags.  If the concrete stack begins with the
first flag and then the second, it is denoted by `cflagComp first second`. -/
public def cflagComp (g : IndexedGrammar T) [Fintype g.nt]
    (first second : CFlag g) : CFlag g :=
  fun A C => decide (∃ B, first A B = true ∧ second B C = true)

namespace CFlag

/-- A compressed relation has at least one usable edge. -/
public def Nonempty {g : IndexedGrammar T} (R : CFlag g) : Prop :=
  ∃ A B, R A B = true

/-- Extensionality specialized to compressed flags. -/
@[ext]
public theorem ext {g : IndexedGrammar T} {R S : CFlag g}
    (h : ∀ A B, R A B = S A B) : R = S := by
  funext A B
  exact h A B

end CFlag

@[simp]
public theorem cflagZero_apply {g : IndexedGrammar T} (A B : g.nt) :
    cflagZero g A B = false := rfl

@[simp]
public theorem cflagBase_apply {g : IndexedGrammar T} (f : g.flag) (A B : g.nt) :
    cflagBase g f A B = true ↔ AugPop g f A B := by
  classical
  simp [cflagBase]

@[simp]
public theorem cflagComp_apply {g : IndexedGrammar T} [Fintype g.nt]
    (first second : CFlag g) (A C : g.nt) :
    cflagComp g first second A C = true ↔
      ∃ B, first A B = true ∧ second B C = true := by
  simp [cflagComp]

public theorem cflagComp_assoc {g : IndexedGrammar T} [Fintype g.nt]
    (R S U : CFlag g) :
    cflagComp g (cflagComp g R S) U = cflagComp g R (cflagComp g S U) := by
  apply CFlag.ext
  intro A D
  apply Bool.eq_iff_iff.mpr
  simp only [cflagComp_apply]
  constructor
  · rintro ⟨C, ⟨B, hAB, hBC⟩, hCD⟩
    exact ⟨B, hAB, C, hBC, hCD⟩
  · rintro ⟨B, hAB, C, hBC, hCD⟩
    exact ⟨C, ⟨B, hAB, hBC⟩, hCD⟩

@[simp]
public theorem cflagComp_zero_left {g : IndexedGrammar T} [Fintype g.nt]
    (R : CFlag g) : cflagComp g (cflagZero g) R = cflagZero g := by
  apply CFlag.ext
  intro A B
  simp [cflagComp, cflagZero]

@[simp]
public theorem cflagComp_zero_right {g : IndexedGrammar T} [Fintype g.nt]
    (R : CFlag g) : cflagComp g R (cflagZero g) = cflagZero g := by
  apply CFlag.ext
  intro A B
  simp [cflagComp, cflagZero]

@[simp]
public theorem cflagZero_not_nonempty {g : IndexedGrammar T} :
    ¬ CFlag.Nonempty (cflagZero g) := by
  simp [CFlag.Nonempty, cflagZero]

public theorem CFlag.eq_zero_iff_not_nonempty {g : IndexedGrammar T} (R : CFlag g) :
    R = cflagZero g ↔ ¬ R.Nonempty := by
  constructor
  · rintro rfl
    exact cflagZero_not_nonempty
  · intro hnot
    apply CFlag.ext
    intro A B
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hnot ⟨A, B, htrue⟩

public theorem cflagComp_nonempty_iff {g : IndexedGrammar T} [Fintype g.nt]
    (R S : CFlag g) :
    (cflagComp g R S).Nonempty ↔
      ∃ A B C, R A B = true ∧ S B C = true := by
  simp only [CFlag.Nonempty, cflagComp_apply]
  constructor
  · rintro ⟨A, C, B, hAB, hBC⟩
    exact ⟨A, B, C, hAB, hBC⟩
  · rintro ⟨A, B, C, hAB, hBC⟩
    exact ⟨A, C, B, hAB, hBC⟩

public theorem cflagComp_nonempty_left {g : IndexedGrammar T} [Fintype g.nt]
    {R S : CFlag g} (h : (cflagComp g R S).Nonempty) : R.Nonempty := by
  rcases (cflagComp_nonempty_iff R S).mp h with ⟨A, B, _C, hAB, _hBC⟩
  exact ⟨A, B, hAB⟩

public theorem cflagComp_nonempty_right {g : IndexedGrammar T} [Fintype g.nt]
    {R S : CFlag g} (h : (cflagComp g R S).Nonempty) : S.Nonempty := by
  rcases (cflagComp_nonempty_iff R S).mp h with ⟨_A, B, C, _hAB, hBC⟩
  exact ⟨B, C, hBC⟩

/-- A base compressed edge is exactly an augmented one-flag pop edge. -/
public theorem cflagBase_edge_derives {g : IndexedGrammar T} {f : g.flag} {A B : g.nt}
    (h : cflagBase g f A B = true) (suffix : List g.flag) :
    g.Derives [ISym.indexed A (f :: suffix)] [ISym.indexed B suffix] :=
  augPop_derives ((cflagBase_apply f A B).mp h) suffix

namespace CFlag

/-- Provenance for a compressed relation.  `Denotes g flags R` records that `R` was built from
the concrete, top-first flag string `flags` by Aho's base relation and relational composition.
It is useful as a soundness invariant for a machine whose finite alphabet contains every Boolean
relation, but whose reachable compressed symbols arise only through `cflagBase` and
`cflagComp`. -/
public inductive Denotes (g : IndexedGrammar T) [Fintype g.nt] :
    List g.flag → CFlag g → Prop where
  | base (f : g.flag) : Denotes g [f] (cflagBase g f)
  | comp {fs gs : List g.flag} {R S : CFlag g}
      (hR : Denotes g fs R) (hS : Denotes g gs S) :
      Denotes g (fs ++ gs) (cflagComp g R S)

namespace Denotes

/-- Every edge of a denoted compressed relation is sound for consuming the represented concrete
flag string above any inherited stack suffix. -/
public theorem edge_derives {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {R : CFlag g} (hden : Denotes g flags R)
    {A B : g.nt} (hedge : R A B = true) (suffix : List g.flag) :
    g.Derives [ISym.indexed A (flags ++ suffix)] [ISym.indexed B suffix] := by
  induction hden generalizing A B suffix with
  | base f =>
      simpa using cflagBase_edge_derives hedge suffix
  | @comp fs gs R S hR hS ihR ihS =>
      rcases (cflagComp_apply _ _ _ _).mp hedge with ⟨C, hAC, hCB⟩
      have hfirst := ihR hAC (gs ++ suffix)
      have hsecond := ihS hCB suffix
      simpa [List.append_assoc] using hfirst.trans hsecond

end Denotes
end CFlag

end Aho
end IndexedGrammar
