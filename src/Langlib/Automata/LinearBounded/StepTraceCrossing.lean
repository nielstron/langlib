module

public import Langlib.Automata.LinearBounded.Definition

@[expose]
public section

/-!
# Finite LBA step traces and tape-boundary crossings

`LBA.Reaches` is a proposition, so it deliberately forgets the finite computation witnessing
reachability.  This file supplies a Type-valued `LBA.StepTrace`: it records the intermediate
configurations of a finite run and supports concatenation and numerical measurements.

For a tape of `n + 1` cells, an element `b : Fin n` names the boundary between cells `b` and
`b + 1`.  A step crosses that boundary to the right when its source head is at or left of `b`
and its target head is strictly right of `b`; crossing to the left is the converse.  The total
crossing count is additive under concatenation.  In particular, every trace whose endpoints lie
on opposite sides of the boundary contains at least one crossing.  When `n = 0` there is no
boundary to choose, so all boundary-indexed statements are vacuous without an extra hypothesis.

The final section gives a reusable simulation operator.  A source step may be represented by an
arbitrary finite target run.  Concatenating those runs lifts a complete source trace, and an
embedding that preserves tape-head positions cannot erase any source boundary crossing.
-/

namespace LBA

universe u v u' v'

variable {Γ : Type u} {Λ : Type v} {n : ℕ}

/-- A concrete finite sequence of `M`-steps with specified endpoints.

Unlike `Reaches M source target`, this lives in `Type` and retains every intermediate
configuration.  The proof of each individual step remains proof-irrelevant. -/
public inductive StepTrace (M : Machine Γ Λ) :
    DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Type (max u v) where
  | refl (cfg : DLBA.Cfg Γ Λ n) : StepTrace M cfg cfg
  | head {source next target : DLBA.Cfg Γ Λ n} :
      Step M source next → StepTrace M next target → StepTrace M source target

namespace StepTrace

variable {M : Machine Γ Λ}
variable {source middle target : DLBA.Cfg Γ Λ n}

/-- The zero-step trace at a configuration. -/
@[expose]
public def nil (cfg : DLBA.Cfg Γ Λ n) : StepTrace M cfg cfg :=
  .refl cfg

/-- Regard one machine step as a one-step trace. -/
@[expose]
public def single (hstep : Step M source target) : StepTrace M source target :=
  .head hstep (.refl target)

/-- Concatenate two finite step traces. -/
@[expose]
public def append : {source middle target : DLBA.Cfg Γ Λ n} →
    StepTrace M source middle → StepTrace M middle target → StepTrace M source target
  | _, _, _, .refl _, second => second
  | _, _, _, .head hstep rest, second => .head hstep (append rest second)

/-- The number of machine steps in a trace. -/
@[expose]
public def length : {source target : DLBA.Cfg Γ Λ n} → StepTrace M source target → ℕ
  | _, _, .refl _ => 0
  | _, _, .head _ rest => length rest + 1

/-- Forget the concrete trace, retaining only reflexive-transitive reachability. -/
@[expose]
public def reaches : {source target : DLBA.Cfg Γ Λ n} →
    StepTrace M source target → Reaches M source target
  | _, _, .refl _ => Relation.ReflTransGen.refl
  | _, _, .head hstep rest => Relation.ReflTransGen.head hstep (reaches rest)

/-- A concrete trace exists exactly when the corresponding configurations are reachable.

`Nonempty` moves the existence assertion back into `Prop` while its witness remains Type-valued.
-/
public theorem nonempty_iff_reaches :
    Nonempty (StepTrace M source target) ↔ Reaches M source target := by
  constructor
  · rintro ⟨trace⟩
    exact trace.reaches
  · intro hreach
    induction hreach with
    | refl => exact ⟨.refl source⟩
    | @tail middle target hreach hstep ih =>
        exact ih.map fun trace => append trace (single hstep)

/-- Choose one concrete finite trace witnessing a reachability proposition.

The choice is necessarily noncomputable because `Reaches` is Prop-valued and may have many
witnessing computations. -/
@[expose]
public noncomputable def ofReaches (hreach : Reaches M source target) :
    StepTrace M source target :=
  Classical.choice (nonempty_iff_reaches.mpr hreach)

@[simp]
public theorem length_refl (cfg : DLBA.Cfg Γ Λ n) :
    length (.refl cfg : StepTrace M cfg cfg) = 0 := rfl

@[simp]
public theorem length_single (hstep : Step M source target) :
    length (single hstep) = 1 := rfl

/-- Trace length is additive under concatenation. -/
@[simp]
public theorem length_append (first : StepTrace M source middle)
    (second : StepTrace M middle target) :
    length (append first second) = length first + length second := by
  induction first with
  | refl => simp [append, length]
  | head hstep rest ih =>
      simp only [append, length, ih]
      omega

/-! ## Boundaries and single-step crossings -/

/-- The head lies at or to the left of the boundary between cells `b` and `b + 1`. -/
@[expose]
public def HeadAtOrLeft (b : Fin n) (cfg : DLBA.Cfg Γ Λ n) : Prop :=
  cfg.tape.head.val ≤ b.val

/-- The head lies strictly to the right of the boundary between cells `b` and `b + 1`. -/
@[expose]
public def HeadRight (b : Fin n) (cfg : DLBA.Cfg Γ Λ n) : Prop :=
  b.val < cfg.tape.head.val

/-- A transition crosses the boundary between cells `b` and `b + 1` from left to right. -/
@[expose]
public def CrossesRight (b : Fin n) (old new : DLBA.Cfg Γ Λ n) : Prop :=
  HeadAtOrLeft b old ∧ HeadRight b new

/-- A transition crosses the boundary between cells `b` and `b + 1` from right to left. -/
@[expose]
public def CrossesLeft (b : Fin n) (old new : DLBA.Cfg Γ Λ n) : Prop :=
  HeadRight b old ∧ HeadAtOrLeft b new

/-- A transition crosses the boundary between cells `b` and `b + 1` in either direction. -/
@[expose]
public def CrossesBoundary (b : Fin n) (old new : DLBA.Cfg Γ Λ n) : Prop :=
  CrossesRight b old new ∨ CrossesLeft b old new

public instance instDecidableCrossesRight (b : Fin n) (old new : DLBA.Cfg Γ Λ n) :
    Decidable (CrossesRight b old new) := by
  unfold CrossesRight HeadAtOrLeft HeadRight
  infer_instance

public instance instDecidableCrossesLeft (b : Fin n) (old new : DLBA.Cfg Γ Λ n) :
    Decidable (CrossesLeft b old new) := by
  unfold CrossesLeft HeadAtOrLeft HeadRight
  infer_instance

public instance instDecidableCrossesBoundary (b : Fin n) (old new : DLBA.Cfg Γ Λ n) :
    Decidable (CrossesBoundary b old new) := by
  unfold CrossesBoundary
  infer_instance

/-- The number of steps of a trace that cross a fixed tape boundary in either direction. -/
@[expose]
public def crossingCount (b : Fin n) :
    {source target : DLBA.Cfg Γ Λ n} → StepTrace M source target → ℕ
  | _, _, .refl _ => 0
  | source, _, .head (next := next) _ rest =>
      (if CrossesBoundary b source next then 1 else 0) + crossingCount b rest

@[simp]
public theorem crossingCount_refl (b : Fin n) (cfg : DLBA.Cfg Γ Λ n) :
    crossingCount b (.refl cfg : StepTrace M cfg cfg) = 0 := rfl

@[simp]
public theorem crossingCount_single (b : Fin n) (hstep : Step M source target) :
    crossingCount b (single hstep) = if CrossesBoundary b source target then 1 else 0 := by
  simp [single, crossingCount]

/-- Boundary-crossing count is additive under concatenation. -/
@[simp]
public theorem crossingCount_append (b : Fin n) (first : StepTrace M source middle)
    (second : StepTrace M middle target) :
    crossingCount b (append first second) =
      crossingCount b first + crossingCount b second := by
  induction first with
  | refl => simp [append, crossingCount]
  | head hstep rest ih =>
      simp only [append, crossingCount, ih]
      omega

/-! ## Endpoint separation forces a crossing -/

/-- A trace from the left side of a boundary to the right side crosses it at least once. -/
public theorem one_le_crossingCount_of_left_right (b : Fin n)
    (trace : StepTrace M source target)
    (hsource : HeadAtOrLeft b source) (htarget : HeadRight b target) :
    1 ≤ crossingCount b trace := by
  induction trace with
  | refl =>
      simp only [HeadAtOrLeft, HeadRight] at hsource htarget
      omega
  | @head source next target hstep rest ih =>
      simp only [crossingCount]
      by_cases hnext : HeadRight b next
      · have hcross : CrossesBoundary b source next :=
          Or.inl ⟨hsource, hnext⟩
        simp only [if_pos hcross]
        omega
      · have hnextLeft : HeadAtOrLeft b next := by
          simp only [HeadAtOrLeft, HeadRight] at hnext ⊢
          omega
        have hrest : 1 ≤ crossingCount b rest := ih hnextLeft htarget
        omega

/-- A trace from the right side of a boundary to the left side crosses it at least once. -/
public theorem one_le_crossingCount_of_right_left (b : Fin n)
    (trace : StepTrace M source target)
    (hsource : HeadRight b source) (htarget : HeadAtOrLeft b target) :
    1 ≤ crossingCount b trace := by
  induction trace with
  | refl =>
      simp only [HeadAtOrLeft, HeadRight] at hsource htarget
      omega
  | @head source next target hstep rest ih =>
      simp only [crossingCount]
      by_cases hnext : HeadAtOrLeft b next
      · have hcross : CrossesBoundary b source next :=
          Or.inr ⟨hsource, hnext⟩
        simp only [if_pos hcross]
        omega
      · have hnextRight : HeadRight b next := by
          simp only [HeadAtOrLeft, HeadRight] at hnext ⊢
          omega
        have hrest : 1 ≤ crossingCount b rest := ih hnextRight htarget
        omega

/-- Endpoint heads on opposite sides of a boundary force at least one crossing, regardless of
orientation. -/
public theorem one_le_crossingCount_of_opposite_sides (b : Fin n)
    (trace : StepTrace M source target)
    (hopposite :
      (HeadAtOrLeft b source ∧ HeadRight b target) ∨
      (HeadRight b source ∧ HeadAtOrLeft b target)) :
    1 ≤ crossingCount b trace := by
  rcases hopposite with hleftRight | hrightLeft
  · exact one_le_crossingCount_of_left_right b trace hleftRight.1 hleftRight.2
  · exact one_le_crossingCount_of_right_left b trace hrightLeft.1 hrightLeft.2

/-! ## Expanding every source step to a target trace -/

variable {Γ' : Type u'} {Λ' : Type v'}
variable {M' : Machine Γ' Λ'}

/-- Lift a concrete trace along a configuration embedding when every source step is simulated by
target reachability.  Each reachability proof is noncomputably turned into a concrete target
trace, and the resulting finite segments are concatenated. -/
@[expose]
public noncomputable def liftByReach
    (embed : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ' Λ' n)
    (stepReach : ∀ ⦃old new⦄, Step M old new → Reaches M' (embed old) (embed new)) :
    {source target : DLBA.Cfg Γ Λ n} →
      StepTrace M source target → StepTrace M' (embed source) (embed target)
  | _, _, .refl _ => .refl _
  | _, _, .head hstep rest =>
      append (ofReaches (stepReach hstep)) (liftByReach embed stepReach rest)

/-- Exact preservation of the head position preserves being on the left side of every boundary. -/
public theorem headAtOrLeft_embed_iff (embed : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ' Λ' n)
    (hhead : ∀ cfg, (embed cfg).tape.head = cfg.tape.head)
    (b : Fin n) (cfg : DLBA.Cfg Γ Λ n) :
    HeadAtOrLeft b (embed cfg) ↔ HeadAtOrLeft b cfg := by
  simp only [HeadAtOrLeft, hhead]

/-- Exact preservation of the head position preserves being on the right side of every boundary. -/
public theorem headRight_embed_iff (embed : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ' Λ' n)
    (hhead : ∀ cfg, (embed cfg).tape.head = cfg.tape.head)
    (b : Fin n) (cfg : DLBA.Cfg Γ Λ n) :
    HeadRight b (embed cfg) ↔ HeadRight b cfg := by
  simp only [HeadRight, hhead]

/-- Replacing each source step by an arbitrary target run cannot erase source boundary crossings
when the configuration embedding preserves the tape head exactly. -/
public theorem crossingCount_le_liftByReach
    (embed : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ' Λ' n)
    (stepReach : ∀ ⦃old new⦄, Step M old new → Reaches M' (embed old) (embed new))
    (hhead : ∀ cfg, (embed cfg).tape.head = cfg.tape.head)
    (b : Fin n) (trace : StepTrace M source target) :
    crossingCount b trace ≤ crossingCount b (liftByReach embed stepReach trace) := by
  induction trace with
  | refl => exact Nat.zero_le _
  | @head source next target hstep rest ih =>
      simp only [crossingCount, liftByReach, crossingCount_append]
      have hsegment :
          (if CrossesBoundary b source next then 1 else 0) ≤
            crossingCount b (ofReaches (stepReach hstep)) := by
        by_cases hcross : CrossesBoundary b source next
        · simp only [if_pos hcross]
          have hopposite :
              (HeadAtOrLeft b (embed source) ∧ HeadRight b (embed next)) ∨
              (HeadRight b (embed source) ∧ HeadAtOrLeft b (embed next)) := by
            rcases hcross with hright | hleft
            · exact Or.inl ⟨
                (headAtOrLeft_embed_iff embed hhead b source).2 hright.1,
                (headRight_embed_iff embed hhead b next).2 hright.2⟩
            · exact Or.inr ⟨
                (headRight_embed_iff embed hhead b source).2 hleft.1,
                (headAtOrLeft_embed_iff embed hhead b next).2 hleft.2⟩
          exact one_le_crossingCount_of_opposite_sides b
            (ofReaches (stepReach hstep)) hopposite
        · simp only [if_neg hcross, Nat.zero_le]
      omega

end StepTrace

end LBA

end
