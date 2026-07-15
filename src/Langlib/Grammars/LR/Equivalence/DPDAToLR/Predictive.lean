module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Construction
public import Langlib.Automata.DeterministicPushdown.Basics.Determinism

/-!
# Predictive first moves of the characteristic PDA

The final-state-to-empty-stack PDA is nondeterministic only at a normalized
final state, where it may either continue simulating the DPDA or enter its
stack-draining state.  For a computation segment with a fixed target state,
one symbol of input lookahead makes the first productive move unique.  The
normalizer's no-repeated-final theorem rules out the sole epsilon/epsilon
ambiguity at end of input.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

public abbrev EState (M : DPDA Q T S) := (Q × Bool) ⊕ Fin 2
public abbrev EStack (M : DPDA Q T S) := Option S

/-- A transition signature records whether the move consumes the leading input
symbol, together with its next control state and replacement stack. -/
public structure FirstMoveSignature (M : DPDA Q T S) where
  consumes : Bool
  nextState : EState M
  replacement : List (EStack M)

/-- A first-move signature is enabled at `(q,input,Z)`. -/
public inductive HasFirstMove (M : DPDA Q T S) (q : EState M) (Z : EStack M) :
    List T → FirstMoveSignature M → Prop
  | read (a : T) (tail : List T) (p : EState M) (alpha : List (EStack M))
      (h : (p, alpha) ∈ (emptyStackPDA M).transition_fun q a Z) :
      HasFirstMove M q Z (a :: tail) ⟨true, p, alpha⟩
  | epsilon (input : List T) (p : EState M) (alpha : List (EStack M))
      (h : (p, alpha) ∈ (emptyStackPDA M).transition_fun' q Z) :
      HasFirstMove M q Z input ⟨false, p, alpha⟩

/-- Remaining input after a move with the given signature. -/
@[expose]
public def inputAfter (M : DPDA Q T S) (sig : FirstMoveSignature M)
    (input : List T) : List T :=
  if sig.consumes then input.drop 1 else input

/-- An enabled first move is productive for a fixed characteristic-nonterminal
target when its successor can net-pop the replacement stack and finish in that
target state. -/
@[expose]
public def ProductiveFirstMove (M : DPDA Q T S) (q : EState M) (Z : EStack M)
    (input : List T) (target : EState M) (sig : FirstMoveSignature M) : Prop :=
  HasFirstMove M q Z input sig ∧
    (emptyStackPDA M).Reaches
      ⟨sig.nextState, inputAfter M sig input, sig.replacement⟩
      ⟨target, [], []⟩

@[simp]
private theorem inputAfter_read (a : T) (w : List T) (p : EState M)
    (alpha : List (EStack M)) :
    inputAfter (Q := Q) (T := T) (S := S) M
      (⟨true, p, alpha⟩ : FirstMoveSignature M) (a :: w) = w := by
  simp [inputAfter]

@[simp]
private theorem inputAfter_epsilon (w : List T) (p : EState M)
    (alpha : List (EStack M)) :
    inputAfter (Q := Q) (T := T) (S := S) M
      (⟨false, p, alpha⟩ : FirstMoveSignature M) w = w := by
  simp [inputAfter]

/-! ## Drain and simulation path facts -/

/-- Once the FS→ES construction enters its drain state, it never changes the
remaining input. -/
public theorem drain_reaches_input_eq (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    {c : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, stack⟩ c) :
    c.input = input := by
  let Inv : PDA.conf (emptyStackPDA M) → Prop := fun d =>
    d.state = Sum.inr 1 ∧ d.input = input
  have hinitial : Inv ⟨Sum.inr 1, input, stack⟩ := ⟨rfl, rfl⟩
  have hpreserve : ∀ {d e : PDA.conf (emptyStackPDA M)},
      Inv d → (emptyStackPDA M).Reaches₁ d e → Inv e := by
    intro d e hd hstep
    rcases d with ⟨state, din, dstack⟩
    rcases hd with ⟨hstate, hinput⟩
    change state = Sum.inr 1 at hstate
    change din = input at hinput
    subst state
    subst din
    cases dstack with
    | nil => simp [PDA.Reaches₁, PDA.step] at hstep
    | cons Z rest =>
        rcases PDA.reaches₁_push hstep with hread | hepsilon
        · rcases hread with ⟨a, tail, next, beta, hnil, he, hmem⟩
          change (next, beta) ∈
            PDA_FS_to_ES_trans M.firstFinal.toPDA (Sum.inr 1) a Z at hmem
          simp [PDA_FS_to_ES_trans] at hmem
        · rcases hepsilon with ⟨next, beta, he, hmem⟩
          subst e
          change (next, beta) ∈
            PDA_FS_to_ES_eps M.firstFinal.toPDA (Sum.inr 1) Z at hmem
          simp only [PDA_FS_to_ES_eps, Set.mem_singleton_iff] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
  have hInv : ∀ (d : PDA.conf (emptyStackPDA M)),
      (emptyStackPDA M).Reaches ⟨Sum.inr 1, input, stack⟩ d → Inv d := by
    intro d hd
    induction hd with
    | refl => exact hinitial
    | tail _ hs ih => exact hpreserve ih hs
  exact (hInv c h).2

/-- A drain first move cannot be productive while a real input symbol remains. -/
private theorem drain_not_productive_nonempty (M : DPDA Q T S)
    (a : T) (w : List T) (stack : List (EStack M)) (target : EState M)
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, a :: w, stack⟩ ⟨target, [], []⟩) : False := by
  have := drain_reaches_input_eq M h
  simp at this

/-- While the FS→ES machine remains in simulation states with a stack made of
`some` symbols, its path projects to the normalized DPDA.  If it reaches the
drain state, some normalized final configuration was reached first. -/
public theorem simulation_reaches_drain_witness (M : DPDA Q T S)
    {q : Q × Bool} {stack : List S}
    {drainStack : List (EStack M)}
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inl q, [], stack.map some⟩
      ⟨Sum.inr 1, [], drainStack⟩) :
    ∃ (p : Q × Bool) (delta : List S),
      p ∈ M.firstFinal.final_states ∧
      M.firstFinal.toPDA.Reaches
        ⟨q, [], stack⟩ ⟨p, [], delta⟩ := by
  let Inv : PDA.conf (emptyStackPDA M) → Prop := fun c =>
    (∃ (p : Q × Bool) (delta : List S),
      c = ⟨Sum.inl p, [], delta.map some⟩ ∧
      M.firstFinal.toPDA.Reaches
        ⟨q, [], stack⟩ ⟨p, [], delta⟩) ∨
    (c.state = Sum.inr 1 ∧ c.input = [] ∧
      ∃ (p : Q × Bool) (delta : List S),
        p ∈ M.firstFinal.final_states ∧
        M.firstFinal.toPDA.Reaches
          ⟨q, [], stack⟩ ⟨p, [], delta⟩)
  have hinitial : Inv ⟨Sum.inl q, [], stack.map some⟩ := by
    exact Or.inl ⟨q, stack, rfl, Relation.ReflTransGen.refl⟩
  have hpreserve : ∀ {c d : PDA.conf (emptyStackPDA M)},
      Inv c → (emptyStackPDA M).Reaches₁ c d → Inv d := by
    intro c d hc hstep
    rcases hc with ⟨p, delta, rfl, hsim⟩ | ⟨hcstate, hcinput, p, delta, hp, hsim⟩
    · cases delta with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons Z rest =>
          rcases PDA.reaches₁_push hstep with hread | hepsilon
          · rcases hread with ⟨a, tail, next, beta, hnil, _⟩
            simp at hnil
          · rcases hepsilon with ⟨next, beta, hd, hmem⟩
            subst d
            change (next, beta) ∈
              PDA_FS_to_ES_eps M.firstFinal.toPDA (Sum.inl p) (some Z) at hmem
            simp only [PDA_FS_to_ES_eps, Set.mem_union] at hmem
            rcases hmem with hsimulation | hdrain
            · rcases hsimulation with ⟨out, hout, heq⟩
              rcases out with ⟨p', replacement⟩
              rcases heq with ⟨rfl, rfl⟩
              have hunder : M.firstFinal.toPDA.Reaches₁
                  ⟨p, [], Z :: rest⟩
                  ⟨p', [], replacement ++ rest⟩ := by
                exact ⟨p', replacement, hout, rfl⟩
              exact Or.inl ⟨p', replacement ++ rest, by simp,
                hsim.tail hunder⟩
            · split_ifs at hdrain with hp
              · have heq : (next, beta) = (Sum.inr 1, []) := by
                  simpa using hdrain
                rcases heq with ⟨rfl, rfl⟩
                exact Or.inr ⟨rfl, rfl, p, Z :: rest, hp, hsim⟩
              · simp at hdrain
    · rcases c with ⟨state, cin, cstack⟩
      simp only at hcstate hcinput
      subst state
      subst cin
      cases cstack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons Z rest =>
          rcases PDA.reaches₁_push hstep with hread | hepsilon
          · rcases hread with ⟨a, tail, next, beta, hnil, _⟩
            simp at hnil
          · rcases hepsilon with ⟨next, beta, hd, hmem⟩
            subst d
            change (next, beta) ∈
              PDA_FS_to_ES_eps M.firstFinal.toPDA (Sum.inr 1) Z at hmem
            simp only [PDA_FS_to_ES_eps, Set.mem_singleton_iff] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact Or.inr ⟨rfl, rfl, p, delta, hp, hsim⟩
  have hInv : ∀ (c : PDA.conf (emptyStackPDA M)),
      (emptyStackPDA M).Reaches
        ⟨Sum.inl q, [], stack.map some⟩ c → Inv c := by
    intro c hc
    induction hc with
    | refl => exact hinitial
    | tail _ hs ih => exact hpreserve ih hs
  have hfinal : Inv ⟨Sum.inr 1, [], drainStack⟩ := hInv _ h
  rcases hfinal with ⟨p, delta, hbad, _⟩ |
      ⟨_, _, p, delta, hp, hsim⟩
  · cases congrArg (fun c => c.state) hbad
  · exact ⟨p, delta, hp, hsim⟩

end

end DPDA_to_LR
