module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Alphabet

@[expose]
public section

/-!
# Aho machine transitions

Zipper configurations, finite composite certificates, and the mathematical transition relation.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Zipper configurations and finite composite certificates -/

/-- A work word with its hatted (active) symbol exposed. -/
public structure WorkCursor (g : IndexedGrammar T) where
  left : List (WorkSym g)
  focus : WorkSym g
  right : List (WorkSym g)

/-- One logical work square, including the unique active-head marker. -/
public structure WorkSlot (g : IndexedGrammar T) where
  active : Bool
  symbol : WorkSym g

public noncomputable instance WorkSlot.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (WorkSlot g) :=
  Classical.decEq _

public noncomputable instance WorkSlot.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (WorkSlot g) := by
  classical
  let encode : WorkSlot g → Bool × WorkSym g := fun s => (s.active, s.symbol)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x
    cases y
    simp_all [encode])

/-- Forget the work head. -/
public def WorkCursor.word {g : IndexedGrammar T} (c : WorkCursor g) : List (WorkSym g) :=
  c.left ++ c.focus :: c.right

/-- Encode the work cursor without losing its active position. -/
public def WorkCursor.slots {g : IndexedGrammar T} (c : WorkCursor g) : List (WorkSlot g) :=
  c.left.map (fun z => ⟨false, z⟩) ++
    ⟨true, c.focus⟩ :: c.right.map (fun z => ⟨false, z⟩)

@[simp] public theorem WorkCursor.slots_length {g : IndexedGrammar T} (c : WorkCursor g) :
    c.slots.length = c.word.length := by
  simp [WorkCursor.slots, WorkCursor.word]

@[simp] public theorem WorkCursor.slots_symbols {g : IndexedGrammar T} (c : WorkCursor g) :
    c.slots.map WorkSlot.symbol = c.word := by
  simp [WorkCursor.slots, WorkCursor.word, List.map_map, Function.comp_def]

/-- The marked slot word retains the whole cursor, not merely its underlying work word. -/
public theorem WorkCursor.slots_injective {g : IndexedGrammar T} :
    Function.Injective (WorkCursor.slots (g := g)) := by
  intro c d h
  rcases c with ⟨left, focus, right⟩
  rcases d with ⟨left', focus', right'⟩
  simp only [WorkCursor.slots] at h
  have falseSlot_injective : Function.Injective
      (fun z : WorkSym g => (⟨false, z⟩ : WorkSlot g)) := by
    intro x y hxy
    exact congrArg WorkSlot.symbol hxy
  induction left generalizing left' with
  | nil =>
      cases left' with
      | nil =>
          simp only [List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hfocus : focus = focus' := congrArg WorkSlot.symbol hhead
          have hright : right = right' :=
            (List.map_injective_iff.mpr falseSlot_injective) htail
          subst focus'
          subst right'
          rfl
      | cons z left' =>
          simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have : true = false := congrArg WorkSlot.active hhead
          contradiction
  | cons z left ih =>
      cases left' with
      | nil =>
          simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have : false = true := congrArg WorkSlot.active hhead
          contradiction
      | cons z' left' =>
          simp only [List.map_cons, List.cons_append] at h
          have hhead := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hz : z = z' := congrArg WorkSlot.symbol hhead
          have hcursor :
              (WorkCursor.mk left focus right : WorkCursor g) =
                WorkCursor.mk left' focus' right' :=
            ih left' htail
          cases hcursor
          cases hz
          rfl

@[simp] public theorem WorkCursor.word_length {g : IndexedGrammar T} (c : WorkCursor g) :
    c.word.length = c.left.length + 1 + c.right.length := by
  simp [WorkCursor.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A composite configuration: `inputPos` input symbols have already been compared, and
`work` is the marked work-tape zipper. -/
public structure Config (g : IndexedGrammar T) where
  inputPos : ℕ
  work : WorkCursor g

/-- The initial composite configuration on every input. -/
public def initialConfig (g : IndexedGrammar T) : Config g :=
  ⟨0, ⟨[WorkSym.dollar], WorkSym.plain g.initial, [WorkSym.hash]⟩⟩

/-- The final composite configuration after all `n` input symbols have been compared. -/
public def finalConfig (g : IndexedGrammar T) (n : ℕ) : Config g :=
  ⟨n, ⟨[WorkSym.dollar], WorkSym.hash, []⟩⟩

/-- Finite evidence selecting one of Aho's composite moves.  All fields range over types fixed
by the grammar, so this is a finite certificate alphabet. -/
public inductive CompositeCert (g : IndexedGrammar T) where
  | plainBinary : g.nt → g.nt → g.nt → CompositeCert g
  | plainTerminal : g.nt → T → CompositeCert g
  | plainPushSkip : g.nt → g.nt → g.flag → CompositeCert g
  | plainPushUse : g.nt → g.nt → g.flag → CompositeCert g
  | liveBinaryBoth : g.nt → g.nt → g.nt → CompositeCert g
  | liveBinaryLeft : g.nt → g.nt → g.nt → CompositeCert g
  | liveBinaryRight : g.nt → g.nt → g.nt → CompositeCert g
  | livePushFresh : g.nt → g.nt → g.flag → CompositeCert g
  | livePushCompress : g.nt → g.nt → g.flag → CFlag g → IndexMark → CompositeCert g
  | popPlain : CFlag g → IndexMark → g.nt → g.nt → CompositeCert g
  | popLive : CFlag g → IndexMark → g.nt → g.nt → CompositeCert g
  | matchTerminal : T → CompositeCert g
  | eraseIndex : CFlag g → IndexMark → CompositeCert g
  | returnFrame : CompositeCert g

public noncomputable instance CompositeCert.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (CompositeCert g) :=
  Classical.decEq _

public noncomputable instance CompositeCert.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] [Fintype g.flag] : Fintype (CompositeCert g) := by
  classical
  letI : Fintype (CFlag g) := by
    change Fintype (g.nt → g.nt → Bool)
    infer_instance
  let encode : CompositeCert g →
      Fin 14 × Option g.nt × Option g.nt × Option g.nt × Option T ×
        Option g.flag × Option (CFlag g) × Option IndexMark
    | .plainBinary A B C =>
        (0, some A, some B, some C, none, none, none, none)
    | .plainTerminal A a =>
        (1, some A, none, none, some a, none, none, none)
    | .plainPushSkip A B f =>
        (2, some A, some B, none, none, some f, none, none)
    | .plainPushUse A B f =>
        (3, some A, some B, none, none, some f, none, none)
    | .liveBinaryBoth A B C =>
        (4, some A, some B, some C, none, none, none, none)
    | .liveBinaryLeft A B C =>
        (5, some A, some B, some C, none, none, none, none)
    | .liveBinaryRight A B C =>
        (6, some A, some B, some C, none, none, none, none)
    | .livePushFresh A B f =>
        (7, some A, some B, none, none, some f, none, none)
    | .livePushCompress A B f R d =>
        (8, some A, some B, none, none, some f, some R, some d)
    | .popPlain R d A B =>
        (9, some A, some B, none, none, none, some R, some d)
    | .popLive R d A B =>
        (10, some A, some B, none, none, none, some R, some d)
    | .matchTerminal a =>
        (11, none, none, none, some a, none, none, none)
    | .eraseIndex R d =>
        (12, none, none, none, none, none, some R, some d)
    | .returnFrame =>
        (13, none, none, none, none, none, none, none)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Semantics of one finite composite certificate on a fixed input word.

The clauses are Aho's moves 1--6, split into their nondeterministic subcases.  The paper's
active hat is represented by `WorkCursor.focus`; consequently every equality below also fixes
the new work-head position. -/
public noncomputable def CertStep (g : IndexedGrammar T) [Fintype g.nt] (input : List T) :
    CompositeCert g → Config g → Config g → Prop
  | .plainBinary A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
              WorkSym.plain C :: beta⟩⟩
  | .plainTerminal A a, c, c' =>
      AugTerminal g A a ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.terminal a, beta⟩⟩
  | .plainPushSkip A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, beta⟩⟩
  | .plainPushUse A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagBase g f) .firstPending :: beta⟩⟩
  | .liveBinaryBoth A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.live C :: Z :: beta⟩⟩
  | .liveBinaryLeft A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.plain C :: Z :: beta⟩⟩
  | .liveBinaryRight A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
              WorkSym.live C :: Z :: beta⟩⟩
  | .livePushFresh A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagBase g f) .laterPending :: Z :: beta⟩⟩
  | .livePushCompress A B f R d, c, c' =>
      AugPush g A B f ∧ (cflagComp g (cflagBase g f) R).Nonempty ∧
        ∃ alpha beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, WorkSym.index R d :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagComp g (cflagBase g f) R) d :: beta⟩⟩
  | .popPlain R d A B, c, c' =>
      R A B = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                beta ++ WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar] ++ beta ++
                  [WorkSym.index R d.markUsed, WorkSym.dollar],
                WorkSym.plain B, WorkSym.close :: gamma⟩⟩) ∨
          (∃ alpha gamma,
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, gamma⟩⟩))
  | .popLive R d A B, c, c' =>
      R A B = true ∧ d.later = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                beta ++ WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar] ++ beta ++
                  [WorkSym.index R d.markUsed, WorkSym.dollar],
                WorkSym.live B, WorkSym.close :: gamma⟩⟩) ∨
          (∃ alpha gamma,
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live B, gamma⟩⟩))
  | .matchTerminal a, c, c' =>
      input[c.inputPos]? = some a ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.terminal a, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos + 1, ⟨alpha ++ [WorkSym.dollar], Z, beta⟩⟩
  | .eraseIndex R d, c, c' =>
      d.erasable = true ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.index R d, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], Z, beta⟩⟩
  | .returnFrame, c, c' =>
      ∃ alpha Z beta gamma,
        Z ≠ WorkSym.dollar ∧ DollarFree beta ∧
        c = ⟨c.inputPos,
          ⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
            WorkSym.close, gamma⟩⟩ ∧
        c' = ⟨c.inputPos,
          ⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩⟩

/-- One composite move is a move selected by some finite certificate. -/
public def CompositeStep (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (c c' : Config g) : Prop :=
  ∃ cert : CompositeCert g, CertStep g input cert c c'

public theorem compositeStep_iff_exists_cert
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T) (c c' : Config g) :
    CompositeStep g input c c' ↔
      ∃ cert : CompositeCert g, CertStep g input cert c c' :=
  Iff.rfl


end Aho
end IndexedGrammar

