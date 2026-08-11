module

public import Langlib.Automata.DeterministicPushdown.Totalization
public import Langlib.Automata.DeterministicPushdown.Basics.Determinism
public import Langlib.Utilities.ComputabilityPredicates
public import Mathlib.Computability.Primrec.List
@[expose]
public section

/-!
# Finite codes for deterministic pushdown automata

`EncodedDPDA T` is raw finite syntax.  States and stack symbols are natural-number
indices, normalized modulo positive sizes when the code is decoded.  Transition
tables are lists; the first matching row is used.  Epsilon transitions have priority,
so every raw code decodes to a genuine `DPDA`, including malformed tables with both
an epsilon row and an input row at the same state and stack top.

The validity promise used by decision problems is semantic totality of the decoded
machine.  This promise is not claimed decidable.  It is the same ordinary promise as
"this program halts on every input": the code is still finite syntax and its step
function remains uniformly effective away from the promise.
-/

open PDA

namespace DPDA

variable {Q Q' T S S' : Type}
  [Fintype Q] [Fintype Q'] [Fintype T] [Fintype S] [Fintype S']

/-- Reindex the finite control and stack alphabets of a DPDA along equivalences. -/
@[expose] public def reindex (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S') :
    DPDA Q' T S' where
  initial_state := eQ M.initial_state
  start_symbol := eS M.start_symbol
  final_states := {q | eQ.symm q ∈ M.final_states}
  transition := fun q a Z =>
    (M.transition (eQ.symm q) a (eS.symm Z)).map fun out =>
      (eQ out.1, out.2.map eS)
  epsilon_transition := fun q Z =>
    (M.epsilon_transition (eQ.symm q) (eS.symm Z)).map fun out =>
      (eQ out.1, out.2.map eS)
  no_mixed := by
    intro q Z hepsilon a
    cases hε : M.epsilon_transition (eQ.symm q) (eS.symm Z) with
    | none => simp [hε] at hepsilon
    | some out =>
        have hmixed := M.no_mixed (eQ.symm q) (eS.symm Z) (by simp [hε]) a
        simp [hε, hmixed]

/-- Map a configuration through a DPDA reindexing. -/
@[expose] public def reindexConf (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    (c : PDA.conf M.toPDA) : PDA.conf (M.reindex eQ eS).toPDA :=
  ⟨eQ c.state, c.input, c.stack.map eS⟩

@[simp] theorem reindexConf_state (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    (c : PDA.conf M.toPDA) : (M.reindexConf eQ eS c).state = eQ c.state := rfl

@[simp] theorem reindexConf_input (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    (c : PDA.conf M.toPDA) : (M.reindexConf eQ eS c).input = c.input := rfl

@[simp] theorem reindexConf_stack (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    (c : PDA.conf M.toPDA) : (M.reindexConf eQ eS c).stack = c.stack.map eS := rfl

private theorem reindex_reaches₁_forward (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    {c d : PDA.conf M.toPDA}
    (h : @PDA.Reaches₁ Q T S _ _ _ M.toPDA c d) :
    @PDA.Reaches₁ Q' T S' _ _ _ (M.reindex eQ eS).toPDA
      (M.reindexConf eQ eS c) (M.reindexConf eQ eS d) := by
  rcases c with ⟨q, input, stack⟩
  rcases d with ⟨p, input', stack'⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      cases input with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA] at h ⊢
          obtain ⟨beta, hbeta, rfl, rfl⟩ := h
          cases hε : M.epsilon_transition q Z with
          | none => simp [hε] at hbeta
          | some out =>
              rcases out with ⟨p₀, beta₀⟩
              have hout : (p, beta) = (p₀, beta₀) := by simpa [hε] using hbeta
              obtain ⟨rfl, rfl⟩ := hout
              exact ⟨eQ p, beta.map eS, by simp [reindex, hε], by
                simp [reindexConf, List.map_append]⟩
      | cons a input =>
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA] at h ⊢
          rcases h with ⟨beta, hbeta, rfl, rfl⟩ | ⟨beta, hbeta, rfl, rfl⟩
          · left
            cases ht : M.transition q a Z with
            | none => simp [ht] at hbeta
            | some out =>
                rcases out with ⟨p₀, beta₀⟩
                have hout : (p, beta) = (p₀, beta₀) := by simpa [ht] using hbeta
                obtain ⟨rfl, rfl⟩ := hout
                exact ⟨eQ p, beta.map eS, by simp [reindex, ht], by
                  simp [reindexConf, List.map_append]⟩
          · right
            cases hε : M.epsilon_transition q Z with
            | none => simp [hε] at hbeta
            | some out =>
                rcases out with ⟨p₀, beta₀⟩
                have hout : (p, beta) = (p₀, beta₀) := by simpa [hε] using hbeta
                obtain ⟨rfl, rfl⟩ := hout
                exact ⟨eQ p, beta.map eS, by simp [reindex, hε], by
                  simp [reindexConf, List.map_append]⟩

private theorem reindex_symm_transition_fun
    (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S') :
    ((M.reindex eQ eS).reindex eQ.symm eS.symm).toPDA.transition_fun =
      M.toPDA.transition_fun := by
  funext q a Z
  cases ht : M.transition q a Z with
  | none => simp [reindex, DPDA.toPDA, ht]
  | some out =>
      rcases out with ⟨p, beta⟩
      simp [reindex, DPDA.toPDA, ht, List.map_map, Function.comp_def]

private theorem reindex_symm_epsilon_transition_fun
    (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S') :
    ((M.reindex eQ eS).reindex eQ.symm eS.symm).toPDA.transition_fun' =
      M.toPDA.transition_fun' := by
  funext q Z
  cases hε : M.epsilon_transition q Z with
  | none => simp [reindex, DPDA.toPDA, hε]
  | some out =>
      rcases out with ⟨p, beta⟩
      simp [reindex, DPDA.toPDA, hε, List.map_map, Function.comp_def]

private theorem reindex_reaches₁_backward (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    {c d : PDA.conf M.toPDA}
    (h : @PDA.Reaches₁ Q' T S' _ _ _ (M.reindex eQ eS).toPDA
      (M.reindexConf eQ eS c) (M.reindexConf eQ eS d)) :
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA c d := by
  rcases c with ⟨q, input, stack⟩
  rcases d with ⟨p, input', stack'⟩
  have hf := reindex_reaches₁_forward (M.reindex eQ eS) eQ.symm eS.symm h
  let M'' := (M.reindex eQ eS).reindex eQ.symm eS.symm
  apply (PDA.reaches1_of_same_transitions M''.toPDA M.toPDA
    (reindex_symm_transition_fun M eQ eS)
    (reindex_symm_epsilon_transition_fun M eQ eS)
    q p input input' stack stack').mp
  simpa [M'', reindexConf, List.map_map, Function.comp_def] using hf

private theorem reindex_reaches_forward (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    {c d : PDA.conf M.toPDA}
    (h : @PDA.Reaches Q T S _ _ _ M.toPDA c d) :
    @PDA.Reaches Q' T S' _ _ _ (M.reindex eQ eS).toPDA
      (M.reindexConf eQ eS c) (M.reindexConf eQ eS d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (reindex_reaches₁_forward M eQ eS hstep)

/-- Reindexing preserves and reflects one-step motion. -/
public theorem reindex_reaches₁_iff (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    {c d : PDA.conf M.toPDA} :
    @PDA.Reaches₁ Q' T S' _ _ _ (M.reindex eQ eS).toPDA
      (M.reindexConf eQ eS c) (M.reindexConf eQ eS d) ↔
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA c d :=
  ⟨reindex_reaches₁_backward M eQ eS, reindex_reaches₁_forward M eQ eS⟩

/-- Reindexing preserves and reflects finite computations. -/
public theorem reindex_reaches_iff (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    {c d : PDA.conf M.toPDA} :
    @PDA.Reaches Q' T S' _ _ _ (M.reindex eQ eS).toPDA
      (M.reindexConf eQ eS c) (M.reindexConf eQ eS d) ↔
    @PDA.Reaches Q T S _ _ _ M.toPDA c d := by
  constructor
  · intro h
    rcases c with ⟨q, input, stack⟩
    rcases d with ⟨p, input', stack'⟩
    have hf := reindex_reaches_forward (M.reindex eQ eS) eQ.symm eS.symm h
    let M'' := (M.reindex eQ eS).reindex eQ.symm eS.symm
    apply PDA.reaches_of_same_transitions M''.toPDA M.toPDA
      (reindex_symm_transition_fun M eQ eS)
      (reindex_symm_epsilon_transition_fun M eQ eS)
      ⟨q, input, stack⟩ ⟨p, input', stack'⟩
    simpa [M'', reindexConf, List.map_map, Function.comp_def] using hf
  · intro h
    exact reindex_reaches_forward M eQ eS h

/-- Reindexing finite state and stack alphabets preserves the accepted language. -/
public theorem reindex_acceptsByFinalState (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S') :
    (M.reindex eQ eS).acceptsByFinalState = M.acceptsByFinalState := by
  ext w
  constructor
  · rintro ⟨q', hq', gamma', hreach⟩
    let q := eQ.symm q'
    let gamma := gamma'.map eS.symm
    have hreach' : @PDA.Reaches Q' T S' _ _ _ (M.reindex eQ eS).toPDA
        (M.reindexConf eQ eS ⟨M.initial_state, w, [M.start_symbol]⟩)
        (M.reindexConf eQ eS ⟨q, [], gamma⟩) := by
      simpa [q, gamma, reindexConf, reindex, List.map_map, Function.comp_def] using hreach
    refine ⟨q, ?_, gamma, (M.reindex_reaches_iff eQ eS).mp hreach'⟩
    change eQ.symm q' ∈ M.final_states
    simpa [reindex] using hq'
  · rintro ⟨q, hq, gamma, hreach⟩
    refine ⟨eQ q, ?_, gamma.map eS, ?_⟩
    · change eQ q ∈ (M.reindex eQ eS).final_states
      simpa [reindex] using hq
    · simpa [reindexConf, reindex] using
        (M.reindex_reaches_iff eQ eS).mpr hreach

/-- Totality is preserved when finite state and stack alphabets are reindexed. -/
public theorem reindex_isTotal (M : DPDA Q T S) (eQ : Q ≃ Q') (eS : S ≃ S')
    (hM : M.IsTotal) : (M.reindex eQ eS).IsTotal := by
  obtain ⟨htotal, hconsistent⟩ := hM
  constructor
  · intro w
    obtain ⟨q, gamma, hreach⟩ := htotal w
    refine ⟨eQ q, gamma.map eS, ?_⟩
    simpa [reindexConf, reindex] using
      (M.reindex_reaches_iff eQ eS).mpr hreach
  · intro w q₁ q₂ gamma₁ gamma₂ h₁ h₂
    let p₁ := eQ.symm q₁
    let p₂ := eQ.symm q₂
    let delta₁ := gamma₁.map eS.symm
    let delta₂ := gamma₂.map eS.symm
    have hr₁ : @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨p₁, [], delta₁⟩ := by
      apply (M.reindex_reaches_iff eQ eS).mp
      simpa [p₁, delta₁, reindexConf, reindex, List.map_map, Function.comp_def] using h₁
    have hr₂ : @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨p₂, [], delta₂⟩ := by
      apply (M.reindex_reaches_iff eQ eS).mp
      simpa [p₂, delta₂, reindexConf, reindex, List.map_map, Function.comp_def] using h₂
    simpa [p₁, p₂, reindex] using
      hconsistent w p₁ p₂ delta₁ delta₂ hr₁ hr₂

end DPDA

namespace DCFEncodedDPDA

/-- One input-transition table row `(source, letter, top, target, replacement)`. -/
public abbrev InputRow (T : Type) := ℕ × T × ℕ × ℕ × List ℕ

/-- One epsilon-transition table row `(source, top, target, replacement)`. -/
public abbrev EpsilonRow := ℕ × ℕ × ℕ × List ℕ

/-- A finite raw code for a deterministic pushdown automaton.

The first two naturals are one less than the state and stack-alphabet sizes, so the
decoded finite types are always inhabited. -/
public def EncodedDPDA (T : Type) :=
  ℕ × ℕ × ℕ × ℕ × List ℕ × List (InputRow T) × List EpsilonRow

namespace EncodedDPDA

variable {T : Type}

public instance [Primcodable T] : Primcodable (EncodedDPDA T) :=
  inferInstanceAs (Primcodable
    (ℕ × ℕ × ℕ × ℕ × List ℕ × List (InputRow T) × List EpsilonRow))

@[expose] public def numStates (c : EncodedDPDA T) : ℕ := c.1 + 1
@[expose] public def numStackSymbols (c : EncodedDPDA T) : ℕ := c.2.1 + 1
@[expose] public def initialIndex (c : EncodedDPDA T) : ℕ := c.2.2.1
@[expose] public def startIndex (c : EncodedDPDA T) : ℕ := c.2.2.2.1
@[expose] public def finalIndices (c : EncodedDPDA T) : List ℕ := c.2.2.2.2.1
@[expose] public def inputRows (c : EncodedDPDA T) : List (InputRow T) := c.2.2.2.2.2.1
@[expose] public def epsilonRows (c : EncodedDPDA T) : List EpsilonRow := c.2.2.2.2.2.2

public theorem numStates_pos (c : EncodedDPDA T) : 0 < c.numStates := by
  simp [numStates]

public theorem numStackSymbols_pos (c : EncodedDPDA T) : 0 < c.numStackSymbols := by
  simp [numStackSymbols]

@[expose] public def state (c : EncodedDPDA T) (q : ℕ) : Fin c.numStates :=
  ⟨q % c.numStates, Nat.mod_lt _ c.numStates_pos⟩

@[expose] public def stackSymbol (c : EncodedDPDA T) (Z : ℕ) : Fin c.numStackSymbols :=
  ⟨Z % c.numStackSymbols, Nat.mod_lt _ c.numStackSymbols_pos⟩

@[expose] public def replacement (c : EncodedDPDA T) (beta : List ℕ) :
    List (Fin c.numStackSymbols) :=
  beta.map c.stackSymbol

/-- The first matching epsilon row, normalized into the decoded finite types. -/
@[expose] public def epsilonLookup [DecidableEq T] (c : EncodedDPDA T)
    (q : Fin c.numStates) (Z : Fin c.numStackSymbols) :
    Option (Fin c.numStates × List (Fin c.numStackSymbols)) :=
  (c.epsilonRows.find? fun r =>
      r.1 % c.numStates = q.val ∧ r.2.1 % c.numStackSymbols = Z.val).map
    fun r => (c.state r.2.2.1, c.replacement r.2.2.2)

/-- The first matching input row, normalized into the decoded finite types. -/
@[expose] public def inputLookup [DecidableEq T] (c : EncodedDPDA T)
    (q : Fin c.numStates) (a : T) (Z : Fin c.numStackSymbols) :
    Option (Fin c.numStates × List (Fin c.numStackSymbols)) :=
  (c.inputRows.find? fun r =>
      r.1 % c.numStates = q.val ∧ r.2.1 = a ∧
        r.2.2.1 % c.numStackSymbols = Z.val).map
    fun r => (c.state r.2.2.2.1, c.replacement r.2.2.2.2)

/-- Decode every raw code to a DPDA.  Epsilon rows take priority over input rows;
this makes the DPDA `no_mixed` invariant hold even for arbitrary raw syntax. -/
@[expose] public def toDPDA [DecidableEq T] [Fintype T] (c : EncodedDPDA T) :
    DPDA (Fin c.numStates) T (Fin c.numStackSymbols) where
  initial_state := c.state c.initialIndex
  start_symbol := c.stackSymbol c.startIndex
  final_states := {q | q.val ∈ c.finalIndices.map (fun n => n % c.numStates)}
  transition := fun q a Z =>
    if c.epsilonLookup q Z |>.isSome then none else c.inputLookup q a Z
  epsilon_transition := c.epsilonLookup
  no_mixed := by
    intro q Z hepsilon a
    change (if (c.epsilonLookup q Z).isSome then none else c.inputLookup q a Z) = none
    have hs : (c.epsilonLookup q Z).isSome = true :=
      Option.isSome_iff_ne_none.mpr hepsilon
    simp [hs]

/-- The language denoted by a raw encoded DPDA. -/
@[expose] public def language [DecidableEq T] [Fintype T]
    (c : EncodedDPDA T) : Language T :=
  c.toDPDA.acceptsByFinalState

/-- Valid decision-problem codes are the raw codes whose decoded machine decides
every input. -/
@[expose] public def Valid [DecidableEq T] [Fintype T]
    (c : EncodedDPDA T) : Prop :=
  c.toDPDA.IsTotal

section Encoding

variable [Fintype T] [DecidableEq T]

/-- Enumerate the defined input transitions of a DPDA whose finite alphabets are
already `Fin`-indexed. -/
@[expose] public noncomputable def encodeInputRows {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) : List (InputRow T) :=
  (Finset.univ : Finset (Fin (n + 1) × T × Fin (m + 1))).toList.filterMap fun x =>
    match M.transition x.1 x.2.1 x.2.2 with
    | none => none
    | some out => some (x.1.val, x.2.1, x.2.2.val,
        out.1.val, out.2.map Fin.val)

/-- Enumerate the defined epsilon transitions of a `Fin`-indexed DPDA. -/
@[expose] public noncomputable def encodeEpsilonRows {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) : List EpsilonRow :=
  (Finset.univ : Finset (Fin (n + 1) × Fin (m + 1))).toList.filterMap fun x =>
    match M.epsilon_transition x.1 x.2 with
    | none => none
    | some out => some (x.1.val, x.2.val, out.1.val, out.2.map Fin.val)

/-- Encode a DPDA whose finite alphabets are already indexed by positive `Fin`
types.  This map is used only to establish adequacy of the raw syntax; decision
algorithms consume the raw code directly. -/
@[expose] public noncomputable def encodeFin {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) : EncodedDPDA T := by
  classical
  exact
    (n, m, M.initial_state.val, M.start_symbol.val,
      ((Finset.univ : Finset (Fin (n + 1))).toList.filter
        (fun q => decide (q ∈ M.final_states))).map Fin.val,
      encodeInputRows M, encodeEpsilonRows M)

@[simp] theorem encodeFin_numStates {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).numStates = n + 1 := rfl

@[simp] theorem encodeFin_numStackSymbols {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).numStackSymbols = m + 1 := rfl

@[simp] theorem encodeFin_state {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (q : Fin (n + 1)) :
    (encodeFin M).state q.val = q := by
  apply Fin.ext
  simp [state, numStates, encodeFin, Nat.mod_eq_of_lt q.isLt]

@[simp] theorem encodeFin_stackSymbol {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (Z : Fin (m + 1)) :
    (encodeFin M).stackSymbol Z.val = Z := by
  apply Fin.ext
  simp [stackSymbol, numStackSymbols, encodeFin, Nat.mod_eq_of_lt Z.isLt]

@[simp] theorem encodeFin_replacement {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (beta : List (Fin (m + 1))) :
    (encodeFin M).replacement (beta.map Fin.val) = beta := by
  simp [replacement, List.map_map, Function.comp_def, encodeFin_stackSymbol]

private theorem mem_encodeEpsilonRows_iff {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (row : EpsilonRow) :
    row ∈ encodeEpsilonRows M ↔
      ∃ q Z p beta, M.epsilon_transition q Z = some (p, beta) ∧
        row = (q.val, Z.val, p.val, beta.map Fin.val) := by
  rw [encodeEpsilonRows, List.mem_filterMap]
  constructor
  · rintro ⟨⟨q, Z⟩, _, hrow⟩
    cases hε : M.epsilon_transition q Z with
    | none => simp [hε] at hrow
    | some out =>
        rcases out with ⟨p, beta⟩
        simp [hε] at hrow
        exact ⟨q, Z, p, beta, hε, hrow.symm⟩
  · rintro ⟨q, Z, p, beta, hε, rfl⟩
    exact ⟨⟨q, Z⟩, by simp, by simp [hε]⟩

private theorem mem_encodeInputRows_iff {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (row : InputRow T) :
    row ∈ encodeInputRows M ↔
      ∃ q a Z p beta, M.transition q a Z = some (p, beta) ∧
        row = (q.val, a, Z.val, p.val, beta.map Fin.val) := by
  rw [encodeInputRows, List.mem_filterMap]
  constructor
  · rintro ⟨⟨q, a, Z⟩, _, hrow⟩
    cases ht : M.transition q a Z with
    | none => simp [ht] at hrow
    | some out =>
        rcases out with ⟨p, beta⟩
        simp [ht] at hrow
        exact ⟨q, a, Z, p, beta, ht, hrow.symm⟩
  · rintro ⟨q, a, Z, p, beta, ht, rfl⟩
    exact ⟨⟨q, a, Z⟩, by simp, by simp [ht]⟩

@[simp] theorem encodeFin_epsilonLookup {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1)))
    (q : Fin (n + 1)) (Z : Fin (m + 1)) :
    (encodeFin M).epsilonLookup q Z = M.epsilon_transition q Z := by
  unfold epsilonLookup
  cases hM : M.epsilon_transition q Z with
  | none =>
      rw [Option.map_eq_none_iff]
      rw [List.find?_eq_none]
      intro row hrow hmatch
      change row ∈ encodeEpsilonRows M at hrow
      rw [mem_encodeEpsilonRows_iff] at hrow
      obtain ⟨q', Z', p, beta, htransition, rfl⟩ := hrow
      simp [encodeFin, numStates, numStackSymbols,
        Nat.mod_eq_of_lt q'.isLt, Nat.mod_eq_of_lt Z'.isLt] at hmatch
      have hq : q' = q := Fin.ext hmatch.1
      have hZ : Z' = Z := Fin.ext hmatch.2
      subst q'
      subst Z'
      exact (by simpa [hM] using htransition)
  | some out =>
      rcases out with ⟨p, beta⟩
      let rows := (encodeFin M).epsilonRows
      let pred : EpsilonRow → Bool := fun r => decide
        (r.1 % (encodeFin M).numStates = q.val ∧
          r.2.1 % (encodeFin M).numStackSymbols = Z.val)
      have hex : ∃ row ∈ rows, pred row = true := by
        refine ⟨(q.val, Z.val, p.val, beta.map Fin.val), ?_, ?_⟩
        · exact (mem_encodeEpsilonRows_iff M _).2 ⟨q, Z, p, beta, hM, rfl⟩
        · simp [pred, encodeFin, numStates, numStackSymbols,
            Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt Z.isLt]
      have hisSome : (rows.find? pred).isSome = true :=
        List.find?_isSome.mpr hex
      cases hfind : rows.find? pred with
      | none => simp [hfind] at hisSome
      | some row =>
          have hrow : row ∈ rows := List.mem_of_find?_eq_some hfind
          have hmatch : pred row = true := List.find?_some hfind
          simp only [Option.map_some]
          change row ∈ encodeEpsilonRows M at hrow
          rw [mem_encodeEpsilonRows_iff] at hrow
          obtain ⟨q', Z', p', beta', ht, rfl⟩ := hrow
          simp [pred, encodeFin, numStates, numStackSymbols,
            Nat.mod_eq_of_lt q'.isLt, Nat.mod_eq_of_lt Z'.isLt] at hmatch
          have hq : q' = q := Fin.ext hmatch.1
          have hZ : Z' = Z := Fin.ext hmatch.2
          subst q'
          subst Z'
          rw [hM] at ht
          obtain ⟨rfl, rfl⟩ := Option.some.inj ht
          simp [encodeFin_state, encodeFin_replacement]

@[simp] theorem encodeFin_inputLookup {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1)))
    (q : Fin (n + 1)) (a : T) (Z : Fin (m + 1)) :
    (encodeFin M).inputLookup q a Z = M.transition q a Z := by
  unfold inputLookup
  cases hM : M.transition q a Z with
  | none =>
      rw [Option.map_eq_none_iff]
      rw [List.find?_eq_none]
      intro row hrow hmatch
      change row ∈ encodeInputRows M at hrow
      rw [mem_encodeInputRows_iff] at hrow
      obtain ⟨q', a', Z', p, beta, htransition, rfl⟩ := hrow
      simp [encodeFin, numStates, numStackSymbols,
        Nat.mod_eq_of_lt q'.isLt, Nat.mod_eq_of_lt Z'.isLt] at hmatch
      have hq : q' = q := Fin.ext hmatch.1
      have hZ : Z' = Z := Fin.ext hmatch.2.2
      have ha : a' = a := hmatch.2.1
      subst q'
      subst Z'
      subst a'
      exact (by simpa [hM] using htransition)
  | some out =>
      rcases out with ⟨p, beta⟩
      let rows := (encodeFin M).inputRows
      let pred : InputRow T → Bool := fun r => decide
        (r.1 % (encodeFin M).numStates = q.val ∧ r.2.1 = a ∧
          r.2.2.1 % (encodeFin M).numStackSymbols = Z.val)
      have hex : ∃ row ∈ rows, pred row = true := by
        refine ⟨(q.val, a, Z.val, p.val, beta.map Fin.val), ?_, ?_⟩
        · exact (mem_encodeInputRows_iff M _).2 ⟨q, a, Z, p, beta, hM, rfl⟩
        · simp [pred, encodeFin, numStates, numStackSymbols,
            Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt Z.isLt]
      have hisSome : (rows.find? pred).isSome = true :=
        List.find?_isSome.mpr hex
      cases hfind : rows.find? pred with
      | none => simp [hfind] at hisSome
      | some row =>
          have hrow : row ∈ rows := List.mem_of_find?_eq_some hfind
          have hmatch : pred row = true := List.find?_some hfind
          simp only [Option.map_some]
          change row ∈ encodeInputRows M at hrow
          rw [mem_encodeInputRows_iff] at hrow
          obtain ⟨q', a', Z', p', beta', ht, rfl⟩ := hrow
          simp [pred, encodeFin, numStates, numStackSymbols,
            Nat.mod_eq_of_lt q'.isLt, Nat.mod_eq_of_lt Z'.isLt] at hmatch
          have hq : q' = q := Fin.ext hmatch.1
          have hZ : Z' = Z := Fin.ext hmatch.2.2
          have ha : a' = a := hmatch.2.1
          subst q'
          subst Z'
          subst a'
          rw [hM] at ht
          obtain ⟨rfl, rfl⟩ := Option.some.inj ht
          simp [encodeFin_state, encodeFin_replacement]

@[simp] theorem encodeFin_final_mem {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (q : Fin (n + 1)) :
    q ∈ (encodeFin M).toDPDA.final_states ↔ q ∈ M.final_states := by
  classical
  simp [toDPDA, finalIndices, encodeFin, numStates,
    Nat.mod_eq_of_lt]
  constructor
  · rintro ⟨r, hr, hval⟩
    have hrq : r = q := Fin.ext (by
      simpa [Nat.mod_eq_of_lt r.isLt] using hval)
    simpa [hrq] using hr
  · intro hq
    exact ⟨q, hq, by simp [Nat.mod_eq_of_lt q.isLt]⟩

@[simp] theorem encodeFin_toDPDA_initial {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).toDPDA.initial_state = M.initial_state :=
  encodeFin_state M M.initial_state

@[simp] theorem encodeFin_toDPDA_start {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).toDPDA.start_symbol = M.start_symbol :=
  encodeFin_stackSymbol M M.start_symbol

@[simp] theorem encodeFin_toDPDA_epsilon {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1)))
    (q : Fin (n + 1)) (Z : Fin (m + 1)) :
    (encodeFin M).toDPDA.epsilon_transition q Z = M.epsilon_transition q Z :=
  encodeFin_epsilonLookup M q Z

@[simp] theorem encodeFin_toDPDA_transition {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1)))
    (q : Fin (n + 1)) (a : T) (Z : Fin (m + 1)) :
    (encodeFin M).toDPDA.transition q a Z = M.transition q a Z := by
  change (if ((encodeFin M).epsilonLookup q Z).isSome then none
    else (encodeFin M).inputLookup q a Z) = M.transition q a Z
  rw [encodeFin_epsilonLookup, encodeFin_inputLookup]
  cases hε : M.epsilon_transition q Z with
  | none => simp [hε]
  | some out =>
      have hmixed := M.no_mixed q Z (by simp [hε]) a
      simp [hε, hmixed]

private theorem encodeFin_transition_fun {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).toDPDA.toPDA.transition_fun = M.toPDA.transition_fun := by
  funext q a Z
  cases ht : M.transition q a Z with
  | none => simp [DPDA.toPDA, ht]
  | some out =>
      rcases out with ⟨p, beta⟩
      simp [DPDA.toPDA, ht]

private theorem encodeFin_epsilon_transition_fun {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    (encodeFin M).toDPDA.toPDA.transition_fun' = M.toPDA.transition_fun' := by
  funext q Z
  cases hε : M.epsilon_transition q Z with
  | none => simp [DPDA.toPDA, hε]
  | some out =>
      rcases out with ⟨p, beta⟩
      simp [DPDA.toPDA, hε]

/-- The canonical raw table has exactly the same finite computations as its
source DPDA. -/
public theorem encodeFin_reaches_iff {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1)))
    (q p : Fin (n + 1)) (u v : List T)
    (gamma delta : List (Fin (m + 1))) :
    @PDA.Reaches _ _ _ _ _ _ (encodeFin M).toDPDA.toPDA
      ⟨q, u, gamma⟩ ⟨p, v, delta⟩ ↔
    @PDA.Reaches _ _ _ _ _ _ M.toPDA
      ⟨q, u, gamma⟩ ⟨p, v, delta⟩ := by
  constructor
  · intro h
    exact PDA.reaches_of_same_transitions _ _
      (encodeFin_transition_fun M) (encodeFin_epsilon_transition_fun M)
      ⟨q, u, gamma⟩ ⟨p, v, delta⟩ h
  · intro h
    exact PDA.reaches_of_same_transitions _ _
      (encodeFin_transition_fun M).symm (encodeFin_epsilon_transition_fun M).symm
      ⟨q, u, gamma⟩ ⟨p, v, delta⟩ h

/-- Encoding a finite `Fin`-indexed DPDA preserves its language. -/
public theorem language_encodeFin {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) :
    language (encodeFin M) = M.acceptsByFinalState := by
  ext w
  constructor
  · rintro ⟨q, hq, gamma, hreach⟩
    refine ⟨q, (encodeFin_final_mem M q).mp hq, gamma, ?_⟩
    change @PDA.Reaches _ _ _ _ _ _ (encodeFin M).toDPDA.toPDA
      ⟨(encodeFin M).toDPDA.initial_state, w,
        [(encodeFin M).toDPDA.start_symbol]⟩ ⟨q, [], gamma⟩ at hreach
    rw [encodeFin_toDPDA_initial, encodeFin_toDPDA_start] at hreach
    exact (encodeFin_reaches_iff M _ _ _ _ _ _).mp hreach
  · rintro ⟨q, hq, gamma, hreach⟩
    refine ⟨q, (encodeFin_final_mem M q).mpr hq, gamma, ?_⟩
    change @PDA.Reaches _ _ _ _ _ _ (encodeFin M).toDPDA.toPDA
      ⟨(encodeFin M).toDPDA.initial_state, w,
        [(encodeFin M).toDPDA.start_symbol]⟩ ⟨q, [], gamma⟩
    rw [encodeFin_toDPDA_initial, encodeFin_toDPDA_start]
    exact (encodeFin_reaches_iff M _ _ _ _ _ _).mpr hreach

/-- Encoding preserves the semantic totality promise. -/
public theorem valid_encodeFin {n m : ℕ}
    (M : DPDA (Fin (n + 1)) T (Fin (m + 1))) (hM : M.IsTotal) :
    Valid (encodeFin M) := by
  unfold Valid DPDA.IsTotal
  obtain ⟨htotal, hconsistent⟩ := hM
  constructor
  · intro w
    obtain ⟨q, gamma, hreach⟩ := htotal w
    refine ⟨q, gamma, ?_⟩
    rw [encodeFin_toDPDA_initial, encodeFin_toDPDA_start]
    exact (encodeFin_reaches_iff M _ _ _ _ _ _).mpr hreach
  · intro w q₁ q₂ gamma₁ gamma₂ h₁ h₂
    rw [encodeFin_final_mem M q₁, encodeFin_final_mem M q₂]
    apply hconsistent w q₁ q₂ gamma₁ gamma₂
    · rw [encodeFin_toDPDA_initial, encodeFin_toDPDA_start] at h₁
      exact (encodeFin_reaches_iff M _ _ _ _ _ _).mp h₁
    · rw [encodeFin_toDPDA_initial, encodeFin_toDPDA_start] at h₂
      exact (encodeFin_reaches_iff M _ _ _ _ _ _).mp h₂

end Encoding

section Adequacy

variable [Fintype T] [DecidableEq T]

/-- Every raw encoded DPDA denotes a deterministic context-free language. -/
public theorem language_isDCF (c : EncodedDPDA T) :
    is_DCF (language c) :=
  ⟨Fin c.numStates, Fin c.numStackSymbols, inferInstance, inferInstance,
    c.toDPDA, rfl⟩

/-- Valid finite DPDA codes present exactly the deterministic context-free
languages.  Completeness first totalizes an arbitrary DPDA presentation, then
reindexes its finite types and records its finite transition tables. -/
public theorem exists_valid_iff_is_DCF (L : Language T) :
    (∃ c : EncodedDPDA T, Valid c ∧ language c = L) ↔ is_DCF L := by
  constructor
  · rintro ⟨c, _, rfl⟩
    exact language_isDCF c
  · rintro ⟨Q, S, hQ, hS, M, hlanguage⟩
    obtain ⟨Q', S', hQ', hS', M', htotal, hequivalent⟩ := M.exists_equivalent_total
    letI : Fintype Q' := hQ'
    letI : Fintype S' := hS'
    have hQpos : 0 < Fintype.card Q' :=
      Fintype.card_pos_iff.mpr ⟨M'.initial_state⟩
    have hSpos : 0 < Fintype.card S' :=
      Fintype.card_pos_iff.mpr ⟨M'.start_symbol⟩
    let eQ : Q' ≃ Fin (Fintype.card Q' - 1 + 1) :=
      (Fintype.equivFin Q').trans
        (finCongr (Nat.succ_pred_eq_of_pos hQpos).symm)
    let eS : S' ≃ Fin (Fintype.card S' - 1 + 1) :=
      (Fintype.equivFin S').trans
        (finCongr (Nat.succ_pred_eq_of_pos hSpos).symm)
    let N := M'.reindex eQ eS
    refine ⟨encodeFin N, ?_, ?_⟩
    · exact valid_encodeFin N (M'.reindex_isTotal eQ eS htotal)
    · rw [language_encodeFin]
      change N.acceptsByFinalState = L
      rw [show N.acceptsByFinalState = M'.acceptsByFinalState from
        M'.reindex_acceptsByFinalState eQ eS]
      rw [hequivalent, hlanguage]

/-- The raw finite-DPDA presentation with the totality promise is adequate for
the class `DCF`. -/
public theorem language_characterizesOn :
    CharacterizesOn DCF (Valid : EncodedDPDA T → Prop)
      (language : EncodedDPDA T → Language T) := by
  intro L
  change is_DCF L ↔ ∃ c : EncodedDPDA T, Valid c ∧ language c = L
  exact (exists_valid_iff_is_DCF L).symm

end Adequacy

end EncodedDPDA

end DCFEncodedDPDA
