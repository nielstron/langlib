module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Rules
public import Langlib.Grammars.LR.Rightmost

/-!
# Rightmost frontiers of the DPDA characteristic grammar

Rightmost derivations in the characteristic grammar have a particularly
rigid frontier.  Every nonterminal strictly before the active (rightmost)
nonterminal is a `single` nonterminal.  The active nonterminal is either
`single` or `list`; the untouched start symbol is handled separately.  These
facts let the DPDA-to-LR proof recover the productive first move represented by
an arbitrary reachable prehandle.
-/

@[expose]
public section

open Language Symbol

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Every nonterminal in a pending prefix is a characteristic `single`
nonterminal.  Terminals may occur anywhere in the prefix. -/
@[expose]
public def PendingPrefix (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) : Prop :=
  ∀ A, symbol.nonterminal A ∈ p →
    ∃ (q t : State M) (Z : StackSymbol M),
      A = PDA_to_CFG.N.single q Z t

public theorem PendingPrefix.nil (M : DPDA Q T S) :
    PendingPrefix M [] := by
  intro A hA
  simp at hA

public theorem PendingPrefix.of_append_left (M : DPDA Q T S)
    {p q : List (symbol T (Nonterminal M))}
    (h : PendingPrefix M (p ++ q)) : PendingPrefix M p := by
  intro A hA
  exact h A (List.mem_append_left q hA)

public theorem PendingPrefix.append_terminals (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (h : PendingPrefix M p)
    (s : List T) :
    PendingPrefix M (p ++ s.map symbol.terminal) := by
  intro A hA
  simp only [List.mem_append, List.mem_map] at hA
  rcases hA with hp | ⟨a, _, ha⟩
  · exact h A hp
  · simp at ha

public theorem PendingPrefix.append_single (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (h : PendingPrefix M p)
    (q t : State M) (Z : StackSymbol M) :
    PendingPrefix M
      (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z t)]) := by
  intro A hA
  simp only [List.mem_append, List.mem_singleton] at hA
  rcases hA with hp | ha
  · exact h A hp
  · have hAeq : A = PDA_to_CFG.N.single q Z t :=
      symbol.nonterminal.inj ha
    exact ⟨q, t, Z, hAeq⟩

/-- Looking from the right, a pending prefix is either entirely terminal or
ends in a `single` nonterminal followed only by terminals. -/
public theorem PendingPrefix.lastView (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (h : PendingPrefix M p) :
    (∃ w : List T, p = w.map symbol.terminal) ∨
    ∃ (p₀ : List (symbol T (Nonterminal M)))
        (q t : State M) (Z : StackSymbol M) (s : List T),
      PendingPrefix M p₀ ∧
      p = p₀ ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z t)] ++
        s.map symbol.terminal := by
  induction p using List.reverseRecOn with
  | nil => exact Or.inl ⟨[], rfl⟩
  | append_singleton p X ih =>
      have hp : PendingPrefix M p :=
        PendingPrefix.of_append_left M h
      cases X with
      | terminal a =>
          rcases ih hp with ⟨w, hw⟩ | ⟨p₀, q, t, Z, s, hp₀, hs⟩
          · left
            exact ⟨w ++ [a], by simp [hw, List.map_append]⟩
          · right
            refine ⟨p₀, q, t, Z, s ++ [a], hp₀, ?_⟩
            simp [hs, List.map_append, List.append_assoc]
      | nonterminal A =>
          obtain ⟨q, t, Z, hA⟩ := h A (by simp)
          subst A
          right
          exact ⟨p, q, t, Z, [], hp, by simp⟩

/-! ## A convenient nonterminal projection -/

private def nonterminalNames (M : DPDA Q T S)
    (w : List (symbol T (Nonterminal M))) : List (Nonterminal M) :=
  w.filterMap fun
    | symbol.terminal _ => none
    | symbol.nonterminal A => some A

@[simp]
private theorem mem_nonterminalNames_iff (M : DPDA Q T S)
    {A : Nonterminal M} {w : List (symbol T (Nonterminal M))} :
    A ∈ nonterminalNames M w ↔ symbol.nonterminal A ∈ w := by
  induction w with
  | nil => simp [nonterminalNames]
  | cons X w ih =>
      unfold nonterminalNames at ih ⊢
      cases X <;> simp_all

@[simp]
private theorem nonterminalNames_map_terminal (M : DPDA Q T S)
    (s : List T) :
    nonterminalNames M (s.map symbol.terminal) = [] := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      simp [nonterminalNames]

@[simp]
private theorem nonterminalNames_prehandle (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (A : Nonterminal M) (s : List T) :
    nonterminalNames M
        (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal) =
      nonterminalNames M p ++ [A] := by
  induction s with
  | nil => simp [nonterminalNames]
  | cons a s ih =>
      simp [nonterminalNames, List.append_assoc]

private theorem pendingPrefix_of_prehandle_eq (M : DPDA Q T S)
    {p p₀ : List (symbol T (Nonterminal M))}
    {A B : Nonterminal M} {s t : List T}
    (hp₀ : PendingPrefix M p₀)
    (heq : p ++ [symbol.nonterminal A] ++ s.map symbol.terminal =
      p₀ ++ [symbol.nonterminal B] ++ t.map symbol.terminal) :
    PendingPrefix M p := by
  have hnames := congrArg (nonterminalNames M) heq
  rw [nonterminalNames_prehandle, nonterminalNames_prehandle] at hnames
  have hpNames : nonterminalNames M p = nonterminalNames M p₀ :=
    List.append_inj_left' hnames (by simp)
  intro C hC
  apply hp₀ C
  rw [← mem_nonterminalNames_iff, ← hpNames,
    mem_nonterminalNames_iff]
  exact hC

private theorem active_eq_of_prehandle_eq (M : DPDA Q T S)
    {p p₀ : List (symbol T (Nonterminal M))}
    {A B : Nonterminal M} {s t : List T}
    (heq : p ++ [symbol.nonterminal A] ++ s.map symbol.terminal =
      p₀ ++ [symbol.nonterminal B] ++ t.map symbol.terminal) :
    A = B := by
  have hnames := congrArg (nonterminalNames M) heq
  rw [nonterminalNames_prehandle, nonterminalNames_prehandle] at hnames
  have hlast : [A] = [B] := List.append_inj_right' hnames (by simp)
  simpa using hlast

/-- The complete shape invariant for a rightmost-reachable characteristic
sentential form. -/
@[expose]
public def CharacteristicFrontier (M : DPDA Q T S)
    (v : List (symbol T (Nonterminal M))) : Prop :=
  v = [symbol.nonterminal PDA_to_CFG.N.start] ∨
  (∃ w : List T, v = w.map symbol.terminal) ∨
  (∃ (p : List (symbol T (Nonterminal M)))
      (q t : State M) (Z : StackSymbol M) (s : List T),
    PendingPrefix M p ∧
    v = p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z t)] ++
      s.map symbol.terminal) ∨
  ∃ (p : List (symbol T (Nonterminal M)))
      (q t : State M) (alpha : List (StackSymbol M)) (s : List T),
    PendingPrefix M p ∧
    v = p ++ [symbol.nonterminal (PDA_to_CFG.N.list q alpha t)] ++
      s.map symbol.terminal

/-- Every prefix before a displayed rightmost nonterminal in a frontier is
pending. -/
public theorem CharacteristicFrontier.pendingPrefix_of_prehandle
    (M : DPDA Q T S) {v p : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {s : List T}
    (hv : CharacteristicFrontier M v)
    (hshape : v = p ++ [symbol.nonterminal A] ++ s.map symbol.terminal) :
    PendingPrefix M p := by
  rcases hv with hstart | hterminal | hsingle | hlist
  · apply pendingPrefix_of_prehandle_eq M (PendingPrefix.nil M)
    have heq :
        p ++ [symbol.nonterminal A] ++ s.map symbol.terminal =
          ([] : List (symbol T (Nonterminal M))) ++
            [symbol.nonterminal PDA_to_CFG.N.start] ++
            ([] : List T).map symbol.terminal := by
      simpa using hshape.symm.trans hstart
    exact heq
  · rcases hterminal with ⟨w, hw⟩
    have hnames := congrArg (nonterminalNames M) (hshape.symm.trans hw)
    rw [nonterminalNames_prehandle, nonterminalNames_map_terminal] at hnames
    simp at hnames
  · rcases hsingle with ⟨p₀, q, t, Z, z, hp₀, hv⟩
    exact pendingPrefix_of_prehandle_eq M hp₀ (hshape.symm.trans hv)
  · rcases hlist with ⟨p₀, q, t, alpha, z, hp₀, hv⟩
    exact pendingPrefix_of_prehandle_eq M hp₀ (hshape.symm.trans hv)

private theorem CharacteristicFrontier.producesRightmost
    (M : DPDA Q T S) {u v : List (symbol T (Nonterminal M))}
    (hu : CharacteristicFrontier M u)
    (hstep : (characteristicGrammar M).ProducesRightmost u v) :
    CharacteristicFrontier M v := by
  rcases hstep with ⟨r, hr, p, s, hsource, htarget⟩
  have hp : PendingPrefix M p :=
    hu.pendingPrefix_of_prehandle M hsource
  rcases characteristicGrammar_rule_shape M hr with
    hepsilon | hread | hepsilonMove | hsplit | hstart
  · rcases hepsilon with ⟨q, rfl⟩
    rw [htarget]
    rcases hp.lastView M with ⟨w, hw⟩ | ⟨p₀, q₀, t₀, Z₀, z, hp₀, hz⟩
    · right
      left
      exact ⟨w ++ s, by simp [hw, List.map_append]⟩
    · right
      right
      left
      refine ⟨p₀, q₀, t₀, Z₀, z ++ s, hp₀, ?_⟩
      simp [hz, List.map_append, List.append_assoc]
  · rcases hread with ⟨q, t, q', a, Z, alpha, _, rfl⟩
    rw [htarget]
    right
    right
    right
    refine ⟨p ++ [symbol.terminal a], q', t, alpha, s,
      ?_, by simp [List.append_assoc]⟩
    simpa using hp.append_terminals M [a]
  · rcases hepsilonMove with ⟨q, t, q', Z, alpha, _, rfl⟩
    rw [htarget]
    right
    right
    right
    exact ⟨p, q', t, alpha, s, hp, by simp⟩
  · rcases hsplit with ⟨q, q', t, Z, alpha, _, rfl⟩
    rw [htarget]
    right
    right
    right
    refine ⟨p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z q')],
      q', t, alpha, s, ?_, by simp [List.append_assoc]⟩
    exact hp.append_single M q q' Z
  · rcases hstart with ⟨t, rfl⟩
    rw [htarget]
    right
    right
    right
    exact ⟨p, (emptyStackPDA M).initial_state, t,
      [(emptyStackPDA M).start_symbol], s, hp, by simp⟩

/-- Every rightmost-reachable sentential form of the reduced characteristic
grammar has the frontier shape above. -/
public theorem derivesRightmost_characteristic_frontier (M : DPDA Q T S)
    {v : List (symbol T (Nonterminal M))}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial] v) :
    CharacteristicFrontier M v := by
  induction h with
  | refl =>
      left
      rw [characteristicGrammar_initial]
  | tail _ hstep ih =>
      exact ih.producesRightmost M hstep

/-- Classification of an arbitrary reachable characteristic prehandle.  The
untouched start case is explicit; otherwise the active nonterminal is either a
`single` or a `list`, and in every case its prefix is pending. -/
public theorem characteristic_prehandle_classification (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M} {s : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    PendingPrefix M p ∧
      ((A = PDA_to_CFG.N.start ∧ p = [] ∧ s = []) ∨
       (∃ (q t : State M) (Z : StackSymbol M),
          A = PDA_to_CFG.N.single q Z t) ∨
       ∃ (q t : State M) (alpha : List (StackSymbol M)),
          A = PDA_to_CFG.N.list q alpha t) := by
  have hf := derivesRightmost_characteristic_frontier M h
  have hp := hf.pendingPrefix_of_prehandle M rfl
  refine ⟨hp, ?_⟩
  rcases hf with hstart | hterminal | hsingle | hlist
  · left
    have heq :
        p ++ [symbol.nonterminal A] ++ s.map symbol.terminal =
          [symbol.nonterminal PDA_to_CFG.N.start] := hstart
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_singleton, List.length_map] at hlen
    have hpNil : p = [] := List.length_eq_zero_iff.mp (by omega)
    have hsNil : s = [] := List.length_eq_zero_iff.mp (by omega)
    have hA : A = PDA_to_CFG.N.start :=
      active_eq_of_prehandle_eq M
        (p := p) (p₀ := []) (A := A) (B := PDA_to_CFG.N.start)
        (s := s) (t := []) (by simpa using hstart)
    exact ⟨hA, hpNil, hsNil⟩
  · rcases hterminal with ⟨w, hw⟩
    have hnames := congrArg (nonterminalNames M) hw
    rw [nonterminalNames_prehandle, nonterminalNames_map_terminal] at hnames
    simp at hnames
  · rcases hsingle with ⟨p₀, q, t, Z, z, hp₀, hv⟩
    right
    left
    exact ⟨q, t, Z, active_eq_of_prehandle_eq M hv⟩
  · rcases hlist with ⟨p₀, q, t, alpha, z, hp₀, hv⟩
    right
    right
    exact ⟨q, t, alpha, active_eq_of_prehandle_eq M hv⟩

/-- Prefix-only form of `characteristic_prehandle_classification`. -/
public theorem pendingPrefix_of_characteristic_prehandle (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M} {s : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    PendingPrefix M p :=
  (characteristic_prehandle_classification M h).1

end

end DPDA_to_LR
