module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories
public import Langlib.Grammars.ContextFree.Toolbox
public import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Utilities.Tactics
import Mathlib.Data.Fintype.Prod

@[expose]
public section

/-!
# Context-free mirror checks for finite pair verifiers

An alternating computation history places one row next to the reversal of the
following row.  A pushdown automaton can therefore compare the two rows while
running any fixed finite-state verifier on corresponding cells.  This file
gives the equivalent finite grammar explicitly, in both orientations.
-/

namespace ContextFree.MalformedHistories

/-- A deterministic finite-state verifier reading two equally long rows in
lockstep. -/
public structure FinitePairVerifier (A Q : Type) where
  start : Q
  step : Q → A → A → Q
  done : Q → Bool

namespace FinitePairVerifier

variable {A Q : Type} (V : FinitePairVerifier A Q)

/-- Run from an arbitrary verifier state.  A length mismatch is rejected
before consulting the final-state test. -/
public def evalFrom : Q → List A → List A → Option Q
  | q, [], [] => some q
  | q, a :: xs, b :: ys => evalFrom (V.step q a b) xs ys
  | _, _, _ => none

public def eval (xs ys : List A) : Option Q :=
  V.evalFrom V.start xs ys

@[simp] public theorem evalFrom_nil (q : Q) :
    V.evalFrom q [] [] = some q := rfl

@[simp] public theorem evalFrom_cons (q : Q) (a b : A)
    (xs ys : List A) :
    V.evalFrom q (a :: xs) (b :: ys) =
      V.evalFrom (V.step q a b) xs ys := rfl

public theorem evalFrom_eq_some_length {q r : Q} {xs ys : List A}
    (h : V.evalFrom q xs ys = some r) : xs.length = ys.length := by
  induction xs generalizing q ys with
  | nil => cases ys <;> simp [evalFrom] at h ⊢
  | cons a xs ih =>
      cases ys with
      | nil => simp [evalFrom] at h
      | cons b ys =>
          simp only [evalFrom] at h
          simpa using ih h

public theorem evalFrom_eq_none_iff (q : Q) (xs ys : List A) :
    V.evalFrom q xs ys = none ↔ xs.length ≠ ys.length := by
  induction xs generalizing q ys with
  | nil => cases ys <;> simp [evalFrom]
  | cons a xs ih =>
      cases ys with
      | nil => simp [evalFrom]
      | cons b ys => simpa [evalFrom] using ih (V.step q a b) ys

public theorem eval_eq_none_iff (xs ys : List A) :
    V.eval xs ys = none ↔ xs.length ≠ ys.length :=
  V.evalFrom_eq_none_iff V.start xs ys

public theorem evalFrom_append_singleton {q r : Q} {xs ys : List A}
    (h : V.evalFrom q xs ys = some r) (a b : A) :
    V.evalFrom q (xs ++ [a]) (ys ++ [b]) = some (V.step r a b) := by
  induction xs generalizing q ys with
  | nil =>
      cases ys with
      | nil => simpa [evalFrom] using congrArg (fun z => Option.map (fun q => V.step q a b) z) h
      | cons y ys => simp [evalFrom] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [evalFrom] at h
      | cons y ys =>
          simp only [List.cons_append, evalFrom] at h ⊢
          exact ih h

/-- The even-pair language: the first row is written forwards and the second
backwards, and the verifier finishes in a rejecting state. -/
public def evenRejectLanguage : Language (Symbol A) :=
  {w | ∃ xs ys q,
    V.eval xs ys = some q ∧ V.done q = false ∧
      w = xs.map Symbol.cell ++
        Symbol.separator :: ys.reverse.map Symbol.cell}

/-- The odd-pair language: the first row is written backwards and the second
forwards, and the verifier finishes in a rejecting state. -/
public def oddRejectLanguage : Language (Symbol A) :=
  {w | ∃ xs ys q,
    V.eval xs ys = some q ∧ V.done q = false ∧
      w = xs.reverse.map Symbol.cell ++
        Symbol.separator :: ys.map Symbol.cell}

/-- The common unequal-width core used in either alternating orientation.
The reversal on the second row is immaterial extensionally, but matches the
forward/backward grammar directly. -/
public def lengthMismatchLanguage (A : Type) : Language (Symbol A) :=
  {w | ∃ xs ys : List A, xs.length ≠ ys.length ∧
    w = xs.map Symbol.cell ++
      Symbol.separator :: ys.reverse.map Symbol.cell}

section Grammar

variable [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]

private def terminalCell (a : A) : symbol (Symbol A) Q :=
  symbol.terminal (.cell a)

private def separatorTerminal : symbol (Symbol A) Q :=
  symbol.terminal .separator

private noncomputable def stepRules : List (Q × List (symbol (Symbol A) Q)) :=
  (Finset.univ : Finset (Q × A × A)).toList.map fun x =>
    (x.1, [terminalCell x.2.1,
      symbol.nonterminal (V.step x.1 x.2.1 x.2.2),
      terminalCell x.2.2])

private noncomputable def stopRules : List (Q × List (symbol (Symbol A) Q)) :=
  ((Finset.univ : Finset Q).filter fun q => V.done q = false).toList.map
    fun q => (q, [separatorTerminal])

/-- The forward grammar expands around the current verifier state. -/
private noncomputable def evenGrammar : CF_grammar (Symbol A) where
  nt := Q
  initial := V.start
  rules := V.stepRules ++ V.stopRules

@[simp] private theorem stepRule_mem (q : Q) (a b : A) :
    (q, [terminalCell a, symbol.nonterminal (V.step q a b), terminalCell b])
      ∈ V.stepRules := by
  unfold stepRules
  rw [List.mem_map]
  exact ⟨(q, a, b), by simp, rfl⟩

@[simp] private theorem stopRule_mem {q : Q} (hq : V.done q = false) :
    (q, [separatorTerminal]) ∈ V.stopRules := by
  simp [stopRules, hq]

private theorem mem_rules_iff {r : Q × List (symbol (Symbol A) Q)} :
    r ∈ V.evenGrammar.rules ↔
      (∃ q a b, r =
        (q, [terminalCell a, symbol.nonterminal (V.step q a b),
          terminalCell b])) ∨
      (∃ q, V.done q = false ∧ r = (q, [separatorTerminal])) := by
  simp only [evenGrammar, List.mem_append]
  constructor
  · rintro (h | h)
    · simp only [stepRules, List.mem_map, Finset.mem_toList,
        Finset.mem_univ, true_and] at h
      obtain ⟨⟨q, a, b⟩, rfl⟩ := h
      exact Or.inl ⟨q, a, b, rfl⟩
    · simp only [stopRules, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨q, a, b, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl (stepRule_mem V q a b)
    · exact Or.inr (stopRule_mem V hq)

private def inProgress (s : List (symbol (Symbol A) Q)) : Prop :=
  ∃ xs ys q, V.eval xs ys = some q ∧
    s = xs.map (symbol.terminal ∘ Symbol.cell) ++
      symbol.nonterminal q :: ys.reverse.map (symbol.terminal ∘ Symbol.cell)

private def completed (s : List (symbol (Symbol A) Q)) : Prop :=
  ∃ xs ys q, V.eval xs ys = some q ∧ V.done q = false ∧
    s = (xs.map Symbol.cell ++
      Symbol.separator :: ys.reverse.map Symbol.cell).map symbol.terminal

private def wellFormed (s : List (symbol (Symbol A) Q)) : Prop :=
  V.inProgress s ∨ V.completed s

private theorem initial_wellFormed :
    V.wellFormed [symbol.nonterminal V.start] := by
  left
  exact ⟨[], [], V.start, rfl, rfl⟩

private theorem inProgress_step {s t : List (symbol (Symbol A) Q)}
    (hs : V.inProgress s) (hst : CF_transforms V.evenGrammar s t) :
    V.wellFormed t := by
  obtain ⟨xs, ys, q, heval, rfl⟩ := hs
  obtain ⟨r, u, v, hr, hbefore, rfl⟩ := hst
  rw [mem_rules_iff] at hr
  have hnotLeft : symbol.nonterminal r.1 ∉
      xs.map (symbol.terminal ∘ Symbol.cell) := by simp
  have hnotRight : symbol.nonterminal r.1 ∉
      ys.reverse.map (symbol.terminal ∘ Symbol.cell) := by simp
  have hbefore' :
      xs.map (symbol.terminal ∘ Symbol.cell) ++
          symbol.nonterminal q :: ys.reverse.map (symbol.terminal ∘ Symbol.cell) =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [List.append_assoc] using hbefore
  have hsplit := (List.append_cons_inj_of_notMem hnotLeft hnotRight).mp hbefore'
  obtain ⟨rfl, hrq, rfl⟩ := hsplit
  rcases hr with ⟨q', a, b, hr⟩ | ⟨q', hdone, hr⟩
  · subst r
    simp only [symbol.nonterminal.injEq] at hrq
    subst q'
    left
    refine ⟨xs ++ [a], ys ++ [b], V.step q a b, ?_, ?_⟩
    · exact evalFrom_append_singleton V heval a b
    · simp [terminalCell, List.map_append, List.reverse_append,
        List.append_assoc]
  · subst r
    simp only [symbol.nonterminal.injEq] at hrq
    subst q'
    right
    refine ⟨xs, ys, q, heval, hdone, ?_⟩
    simp [separatorTerminal, List.map_append]

private theorem completed_no_step {s t : List (symbol (Symbol A) Q)}
    (hs : V.completed s) : ¬ CF_transforms V.evenGrammar s t := by
  rintro ⟨r, u, v, -, hbefore, -⟩
  obtain ⟨xs, ys, q, -, -, rfl⟩ := hs
  have hn : symbol.nonterminal r.1 ∈
      (xs.map Symbol.cell ++
        Symbol.separator :: ys.reverse.map Symbol.cell).map symbol.terminal := by
    rw [hbefore]
    simp
  simpa using hn

private theorem wellFormed_step {s t : List (symbol (Symbol A) Q)}
    (hs : V.wellFormed s) (hst : CF_transforms V.evenGrammar s t) :
    V.wellFormed t := by
  rcases hs with hs | hs
  · exact inProgress_step V hs hst
  · exact (completed_no_step V hs hst).elim

private theorem wellFormed_of_derives {s : List (symbol (Symbol A) Q)}
    (h : CF_derives V.evenGrammar [symbol.nonterminal V.start] s) :
    V.wellFormed s := by
  induction h with
  | refl => exact initial_wellFormed V
  | tail _ hstep ih => exact wellFormed_step V ih hstep

private theorem evenGrammar_sound :
    CF_language V.evenGrammar ≤ V.evenRejectLanguage := by
  intro w hw
  have hform := wellFormed_of_derives V hw
  rcases hform with ⟨xs, ys, q, -, heq⟩ | ⟨xs, ys, q, heval, hdone, heq⟩
  · have hn : symbol.nonterminal q ∈ w.map symbol.terminal := by
      rw [heq]
      simp
    simpa using hn
  · refine ⟨xs, ys, q, heval, hdone, ?_⟩
    exact (Function.Injective.list_map fun _ _ h => symbol.terminal.inj h) heq

private theorem derive_steps (xs ys : List A) (q : Q)
    (heval : V.evalFrom q xs ys = some r) :
    CF_derives V.evenGrammar [symbol.nonterminal q]
      (xs.map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal r :: ys.reverse.map
          (symbol.terminal ∘ Symbol.cell)) := by
  induction xs generalizing q ys with
  | nil =>
      cases ys with
      | nil =>
          simp only [evalFrom, Option.some.injEq] at heval
          subst r
          exact CF_deri_self
      | cons y ys => simp [evalFrom] at heval
  | cons x xs ih =>
      cases ys with
      | nil => simp [evalFrom] at heval
      | cons y ys =>
          simp only [evalFrom] at heval
          apply CF_deri_of_tran_deri
          · exact ⟨(q, [terminalCell x,
                symbol.nonterminal (V.step q x y), terminalCell y]),
              [], [], (mem_rules_iff V).2 (Or.inl ⟨q, x, y, rfl⟩), rfl, rfl⟩
          · have hinner := ih (q := V.step q x y) (ys := ys) heval
            have hcontext := CF_deri_with_prefix_and_postfix
              [terminalCell x] [terminalCell y] hinner
            simpa [terminalCell, List.reverse_cons, List.map_append,
              List.append_assoc] using hcontext

private theorem evenGrammar_complete :
    V.evenRejectLanguage ≤ CF_language V.evenGrammar := by
  intro w hw
  obtain ⟨xs, ys, q, heval, hdone, rfl⟩ := hw
  have hsteps := derive_steps V xs ys V.start heval
  have hstop : CF_derives V.evenGrammar
      (xs.map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal q :: ys.reverse.map
          (symbol.terminal ∘ Symbol.cell))
      ((xs.map Symbol.cell ++ Symbol.separator ::
        ys.reverse.map Symbol.cell).map symbol.terminal) := by
    apply CF_deri_of_tran
    refine ⟨(q, [separatorTerminal]),
      xs.map (symbol.terminal ∘ Symbol.cell),
      ys.reverse.map (symbol.terminal ∘ Symbol.cell),
      ?_, ?_, ?_⟩
    · exact (mem_rules_iff V).2 (Or.inr ⟨q, hdone, rfl⟩)
    · simp [List.append_assoc]
    · simp [separatorTerminal, List.map_append]
  exact CF_deri_of_deri_deri hsteps hstop

/-- Every finite rejecting mirror relation in the forward/backward orientation
is context-free. -/
public theorem evenRejectLanguage_is_CF : is_CF V.evenRejectLanguage := by
  apply is_CF_via_cfg_implies_is_CF
  exact ⟨V.evenGrammar, Set.Subset.antisymm (evenGrammar_sound V)
    (evenGrammar_complete V)⟩

/-! ## The backward/forward orientation -/

private def oddTerminalCell (a : A) : symbol (Symbol A) (Option Q) :=
  symbol.terminal (.cell a)

private def oddSeparatorTerminal : symbol (Symbol A) (Option Q) :=
  symbol.terminal .separator

private noncomputable def oddChoiceRules :
    List (Option Q × List (symbol (Symbol A) (Option Q))) :=
  ((Finset.univ : Finset Q).filter fun q => V.done q = false).toList.map
    fun q => (none, [symbol.nonterminal (some q)])

private noncomputable def oddBackRules :
    List (Option Q × List (symbol (Symbol A) (Option Q))) :=
  (Finset.univ : Finset (Q × A × A)).toList.map fun x =>
    (some (V.step x.1 x.2.1 x.2.2),
      [oddTerminalCell x.2.1, symbol.nonterminal (some x.1),
        oddTerminalCell x.2.2])

private def oddStopRules :
    List (Option Q × List (symbol (Symbol A) (Option Q))) :=
  [(some V.start, [oddSeparatorTerminal])]

private noncomputable def oddGrammar : CF_grammar (Symbol A) where
  nt := Option Q
  initial := none
  rules := V.oddChoiceRules ++ (V.oddBackRules ++ V.oddStopRules)

private theorem odd_mem_rules_iff
    {r : Option Q × List (symbol (Symbol A) (Option Q))} :
    r ∈ V.oddGrammar.rules ↔
      (∃ q, V.done q = false ∧
        r = (none, [symbol.nonterminal (some q)])) ∨
      (∃ q a b, r =
        (some (V.step q a b),
          [oddTerminalCell a, symbol.nonterminal (some q),
            oddTerminalCell b])) ∨
      r = (some V.start, [oddSeparatorTerminal]) := by
  simp only [oddGrammar, List.mem_append]
  constructor
  · intro h
    rcases h with hChoice | hRest
    · simp only [oddChoiceRules, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hChoice
      obtain ⟨q, hq, rfl⟩ := hChoice
      exact Or.inl ⟨q, hq, rfl⟩
    · rcases hRest with hBack | hStop
      · simp only [oddBackRules, List.mem_map, Finset.mem_toList,
          Finset.mem_univ, true_and] at hBack
        obtain ⟨⟨q, a, b⟩, rfl⟩ := hBack
        exact Or.inr (Or.inl ⟨q, a, b, rfl⟩)
      · have : r = (some V.start, [oddSeparatorTerminal]) := by
          simpa [oddStopRules] using hStop
        exact Or.inr (Or.inr this)
  · intro h
    rcases h with hChoice | hRest
    · obtain ⟨q, hq, rfl⟩ := hChoice
      left
      unfold oddChoiceRules
      rw [List.mem_map]
      exact ⟨q, by simp [hq], rfl⟩
    · rcases hRest with hBack | hStop
      · obtain ⟨q, a, b, rfl⟩ := hBack
        right; left
        unfold oddBackRules
        rw [List.mem_map]
        exact ⟨(q, a, b), by simp, rfl⟩
      · subst r
        right; right
        simp [oddStopRules]

private def oddInProgress
    (s : List (symbol (Symbol A) (Option Q))) : Prop :=
  ∃ xs ys p final,
    V.evalFrom p xs ys = some final ∧ V.done final = false ∧
      s = xs.reverse.map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal (some p) ::
          ys.map (symbol.terminal ∘ Symbol.cell)

private def oddCompleted
    (s : List (symbol (Symbol A) (Option Q))) : Prop :=
  ∃ xs ys final,
    V.eval xs ys = some final ∧ V.done final = false ∧
      s = (xs.reverse.map Symbol.cell ++
        Symbol.separator :: ys.map Symbol.cell).map symbol.terminal

private def oddWellFormed
    (s : List (symbol (Symbol A) (Option Q))) : Prop :=
  s = [symbol.nonterminal none] ∨ V.oddInProgress s ∨ V.oddCompleted s

private theorem odd_initial_wellFormed :
    V.oddWellFormed [symbol.nonterminal none] := Or.inl rfl

private theorem odd_root_step {t : List (symbol (Symbol A) (Option Q))}
    (hst : CF_transforms V.oddGrammar [symbol.nonterminal none] t) :
    V.oddWellFormed t := by
  obtain ⟨r, u, v, hr, hbefore, rfl⟩ := hst
  have hbefore' :
      ([] : List (symbol (Symbol A) (Option Q))) ++
          symbol.nonterminal none :: [] =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [List.append_assoc] using hbefore
  have hsplit := (List.append_cons_inj_of_notMem
    (by simp : symbol.nonterminal r.1 ∉
      ([] : List (symbol (Symbol A) (Option Q))))
    (by simp : symbol.nonterminal r.1 ∉
      ([] : List (symbol (Symbol A) (Option Q))))).mp hbefore'
  obtain ⟨rfl, hrnone, rfl⟩ := hsplit
  rw [odd_mem_rules_iff] at hr
  rcases hr with ⟨q, hdone, hr⟩ | ⟨q, a, b, hr⟩ | hr
  · subst r
    right; left
    exact ⟨[], [], q, q, rfl, hdone, rfl⟩
  · subst r
    simp at hrnone
  · subst r
    simp at hrnone

private theorem odd_progress_step
    {s t : List (symbol (Symbol A) (Option Q))}
    (hs : V.oddInProgress s) (hst : CF_transforms V.oddGrammar s t) :
    V.oddWellFormed t := by
  obtain ⟨xs, ys, p, final, heval, hdone, rfl⟩ := hs
  obtain ⟨r, u, v, hr, hbefore, rfl⟩ := hst
  have hnotLeft : symbol.nonterminal r.1 ∉
      xs.reverse.map (symbol.terminal ∘ Symbol.cell) := by simp
  have hnotRight : symbol.nonterminal r.1 ∉
      ys.map (symbol.terminal ∘ Symbol.cell) := by simp
  have hbefore' :
      xs.reverse.map (symbol.terminal ∘ Symbol.cell) ++
          symbol.nonterminal (some p) ::
            ys.map (symbol.terminal ∘ Symbol.cell) =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [List.append_assoc] using hbefore
  have hsplit := (List.append_cons_inj_of_notMem hnotLeft hnotRight).mp hbefore'
  obtain ⟨rfl, hrp, rfl⟩ := hsplit
  rw [odd_mem_rules_iff] at hr
  rcases hr with ⟨q, hqdone, hr⟩ | ⟨q, a, b, hr⟩ | hr
  · subst r
    simp at hrp
  · subst r
    simp only [symbol.nonterminal.injEq, Option.some.injEq] at hrp
    right; left
    refine ⟨a :: xs, b :: ys, q, final, ?_, hdone, ?_⟩
    · simpa [evalFrom, hrp] using heval
    · simp [oddTerminalCell, List.reverse_cons, List.map_append,
        List.append_assoc, hrp]
  · subst r
    simp only [symbol.nonterminal.injEq, Option.some.injEq] at hrp
    subst p
    right; right
    exact ⟨xs, ys, final, heval, hdone, by
      simp [oddSeparatorTerminal, List.map_append]⟩

private theorem odd_completed_no_step
    {s t : List (symbol (Symbol A) (Option Q))}
    (hs : V.oddCompleted s) : ¬ CF_transforms V.oddGrammar s t := by
  rintro ⟨r, u, v, -, hbefore, -⟩
  obtain ⟨xs, ys, final, -, -, rfl⟩ := hs
  have hn : symbol.nonterminal r.1 ∈
      (xs.reverse.map Symbol.cell ++
        Symbol.separator :: ys.map Symbol.cell).map symbol.terminal := by
    rw [hbefore]
    simp
  simpa using hn

private theorem odd_wellFormed_step
    {s t : List (symbol (Symbol A) (Option Q))}
    (hs : V.oddWellFormed s) (hst : CF_transforms V.oddGrammar s t) :
    V.oddWellFormed t := by
  rcases hs with rfl | hs | hs
  · exact odd_root_step V hst
  · exact odd_progress_step V hs hst
  · exact (odd_completed_no_step V hs hst).elim

private theorem odd_wellFormed_of_derives
    {s : List (symbol (Symbol A) (Option Q))}
    (h : CF_derives V.oddGrammar [symbol.nonterminal none] s) :
    V.oddWellFormed s := by
  induction h with
  | refl => exact odd_initial_wellFormed V
  | tail _ hstep ih => exact odd_wellFormed_step V ih hstep

private theorem oddGrammar_sound :
    CF_language V.oddGrammar ≤ V.oddRejectLanguage := by
  intro w hw
  have hform := odd_wellFormed_of_derives V hw
  rcases hform with hroot | hprogress | hcomplete
  · have hn : symbol.nonterminal (none : Option Q) ∈
        w.map (fun a => (symbol.terminal a :
          symbol (Symbol A) (Option Q))) := by
      rw [hroot]
      simp
    simpa using hn
  · obtain ⟨xs, ys, p, final, -, -, heq⟩ := hprogress
    have hn : symbol.nonterminal (some p) ∈ w.map symbol.terminal := by
      rw [heq]
      simp
    simpa using hn
  · obtain ⟨xs, ys, final, heval, hdone, heq⟩ := hcomplete
    exact ⟨xs, ys, final, heval, hdone,
      (Function.Injective.list_map fun _ _ h => symbol.terminal.inj h) heq⟩

private theorem derive_backwards (xs ys : List A) (p final : Q)
    (heval : V.evalFrom p xs ys = some final) :
    CF_derives V.oddGrammar [symbol.nonterminal (some final)]
      (xs.reverse.map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal (some p) ::
          ys.map (symbol.terminal ∘ Symbol.cell)) := by
  induction xs generalizing p ys with
  | nil =>
      cases ys with
      | nil =>
          simp only [evalFrom, Option.some.injEq] at heval
          subst final
          exact CF_deri_self
      | cons y ys => simp [evalFrom] at heval
  | cons x xs ih =>
      cases ys with
      | nil => simp [evalFrom] at heval
      | cons y ys =>
          simp only [evalFrom] at heval
          have hinner := ih (p := V.step p x y) (ys := ys) heval
          apply CF_deri_of_deri_tran hinner
          refine ⟨(some (V.step p x y),
              [oddTerminalCell x, symbol.nonterminal (some p), oddTerminalCell y]),
            xs.reverse.map (symbol.terminal ∘ Symbol.cell),
            ys.map (symbol.terminal ∘ Symbol.cell), ?_, ?_, ?_⟩
          · exact (odd_mem_rules_iff V).2
              (Or.inr (Or.inl ⟨p, x, y, rfl⟩))
          · simp [List.append_assoc]
          · simp [oddTerminalCell, List.reverse_cons, List.map_append,
              List.append_assoc]

private theorem oddGrammar_complete :
    V.oddRejectLanguage ≤ CF_language V.oddGrammar := by
  intro w hw
  obtain ⟨xs, ys, final, heval, hdone, rfl⟩ := hw
  have hchoose : CF_derives V.oddGrammar
      [symbol.nonterminal none] [symbol.nonterminal (some final)] := by
    apply CF_deri_of_tran
    exact ⟨(none, [symbol.nonterminal (some final)]), [], [],
      (odd_mem_rules_iff V).2 (Or.inl ⟨final, hdone, rfl⟩), rfl, rfl⟩
  have hback := derive_backwards V xs ys V.start final heval
  have hstop : CF_derives V.oddGrammar
      (xs.reverse.map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal (some V.start) ::
          ys.map (symbol.terminal ∘ Symbol.cell))
      ((xs.reverse.map Symbol.cell ++ Symbol.separator ::
        ys.map Symbol.cell).map symbol.terminal) := by
    apply CF_deri_of_tran
    refine ⟨(some V.start, [oddSeparatorTerminal]),
      xs.reverse.map (symbol.terminal ∘ Symbol.cell),
      ys.map (symbol.terminal ∘ Symbol.cell), ?_, ?_, ?_⟩
    · exact (odd_mem_rules_iff V).2 (Or.inr (Or.inr rfl))
    · simp [List.append_assoc]
    · simp [oddSeparatorTerminal, List.map_append]
  exact CF_deri_of_deri_deri hchoose (CF_deri_of_deri_deri hback hstop)

/-- Every finite rejecting mirror relation in the backward/forward orientation
is context-free. -/
public theorem oddRejectLanguage_is_CF : is_CF V.oddRejectLanguage := by
  apply is_CF_via_cfg_implies_is_CF
  exact ⟨V.oddGrammar, Set.Subset.antisymm (oddGrammar_sound V)
    (oddGrammar_complete V)⟩

/-! ## Unequal row lengths -/

private inductive MismatchNT where
  | pair
  | left
  | right
  deriving DecidableEq, Fintype

private def mismatchCell (a : A) : symbol (Symbol A) MismatchNT :=
  symbol.terminal (.cell a)

private def mismatchSeparator : symbol (Symbol A) MismatchNT :=
  symbol.terminal .separator

private noncomputable def mismatchPairRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  (Finset.univ : Finset (A × A)).toList.map fun x =>
    (.pair, [mismatchCell x.1, symbol.nonterminal .pair,
      mismatchCell x.2])

private noncomputable def mismatchLeftBeginRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  (Finset.univ : Finset A).toList.map fun a =>
    (.pair, [mismatchCell a, symbol.nonterminal .left])

private noncomputable def mismatchLeftMoreRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  (Finset.univ : Finset A).toList.map fun a =>
    (.left, [mismatchCell a, symbol.nonterminal .left])

private noncomputable def mismatchRightBeginRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  (Finset.univ : Finset A).toList.map fun b =>
    (.pair, [mismatchSeparator, mismatchCell b,
      symbol.nonterminal .right])

private noncomputable def mismatchRightMoreRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  (Finset.univ : Finset A).toList.map fun b =>
    (.right, [mismatchCell b, symbol.nonterminal .right])

private def mismatchStopRules :
    List (MismatchNT × List (symbol (Symbol A) MismatchNT)) :=
  [(.left, [mismatchSeparator]), (.right, [])]

private noncomputable def mismatchGrammar : CF_grammar (Symbol A) where
  nt := MismatchNT
  initial := .pair
  rules := mismatchPairRules ++ (mismatchLeftBeginRules ++
    (mismatchLeftMoreRules ++ (mismatchRightBeginRules ++
      (mismatchRightMoreRules ++ mismatchStopRules))))

private theorem mismatch_mem_rules_iff
    {r : MismatchNT × List (symbol (Symbol A) MismatchNT)} :
    r ∈ (mismatchGrammar (A := A)).rules ↔
      (∃ a b, r = (.pair,
        [mismatchCell a, symbol.nonterminal .pair, mismatchCell b])) ∨
      (∃ a, r = (.pair, [mismatchCell a, symbol.nonterminal .left])) ∨
      (∃ a, r = (.left, [mismatchCell a, symbol.nonterminal .left])) ∨
      (∃ b, r = (.pair,
        [mismatchSeparator, mismatchCell b, symbol.nonterminal .right])) ∨
      (∃ b, r = (.right, [mismatchCell b, symbol.nonterminal .right])) ∨
      r = (.left, [mismatchSeparator]) ∨ r = (.right, []) := by
  simp only [mismatchGrammar, List.mem_append]
  constructor
  · intro h
    rcases h with hp | h
    · simp only [mismatchPairRules, List.mem_map, Finset.mem_toList,
        Finset.mem_univ, true_and] at hp
      obtain ⟨⟨a, b⟩, rfl⟩ := hp
      exact Or.inl ⟨a, b, rfl⟩
    · rcases h with hlb | h
      · simp only [mismatchLeftBeginRules, List.mem_map,
          Finset.mem_toList, Finset.mem_univ, true_and] at hlb
        obtain ⟨a, rfl⟩ := hlb
        exact Or.inr (Or.inl ⟨a, rfl⟩)
      · rcases h with hlm | h
        · simp only [mismatchLeftMoreRules, List.mem_map,
            Finset.mem_toList, Finset.mem_univ, true_and] at hlm
          obtain ⟨a, rfl⟩ := hlm
          exact Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))
        · rcases h with hrb | h
          · simp only [mismatchRightBeginRules, List.mem_map,
              Finset.mem_toList, Finset.mem_univ, true_and] at hrb
            obtain ⟨b, rfl⟩ := hrb
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b, rfl⟩)))
          · rcases h with hrm | hs
            · simp only [mismatchRightMoreRules, List.mem_map,
                Finset.mem_toList, Finset.mem_univ, true_and] at hrm
              obtain ⟨b, rfl⟩ := hrm
              exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨b, rfl⟩))))
            · simp only [mismatchStopRules, List.mem_cons,
                List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl rfl)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr rfl)))))
  · intro h
    rcases h with hp | h
    · obtain ⟨a, b, rfl⟩ := hp
      left
      unfold mismatchPairRules
      rw [List.mem_map]
      exact ⟨(a, b), by simp, rfl⟩
    · right
      rcases h with hlb | h
      · obtain ⟨a, rfl⟩ := hlb
        left
        unfold mismatchLeftBeginRules
        rw [List.mem_map]
        exact ⟨a, by simp, rfl⟩
      · right
        rcases h with hlm | h
        · obtain ⟨a, rfl⟩ := hlm
          left
          unfold mismatchLeftMoreRules
          rw [List.mem_map]
          exact ⟨a, by simp, rfl⟩
        · right
          rcases h with hrb | h
          · obtain ⟨b, rfl⟩ := hrb
            left
            unfold mismatchRightBeginRules
            rw [List.mem_map]
            exact ⟨b, by simp, rfl⟩
          · right
            rcases h with hrm | hs
            · obtain ⟨b, rfl⟩ := hrm
              left
              unfold mismatchRightMoreRules
              rw [List.mem_map]
              exact ⟨b, by simp, rfl⟩
            · right
              simpa [mismatchStopRules] using hs

private def mismatchPairProgress
    (s : List (symbol (Symbol A) MismatchNT)) : Prop :=
  ∃ xs ys : List A, xs.length = ys.length ∧
    s = xs.map (symbol.terminal ∘ Symbol.cell) ++
      symbol.nonterminal .pair ::
        ys.reverse.map (symbol.terminal ∘ Symbol.cell)

private def mismatchLeftProgress
    (s : List (symbol (Symbol A) MismatchNT)) : Prop :=
  ∃ xs ys extra : List A,
    xs.length = ys.length ∧ extra ≠ [] ∧
      s = (xs ++ extra).map (symbol.terminal ∘ Symbol.cell) ++
        symbol.nonterminal .left ::
          ys.reverse.map (symbol.terminal ∘ Symbol.cell)

private def mismatchRightProgress
    (s : List (symbol (Symbol A) MismatchNT)) : Prop :=
  ∃ xs ys extra : List A,
    xs.length = ys.length ∧ extra ≠ [] ∧
      s = xs.map (symbol.terminal ∘ Symbol.cell) ++
        mismatchSeparator ::
          (extra.map (symbol.terminal ∘ Symbol.cell) ++
            symbol.nonterminal .right ::
              ys.reverse.map (symbol.terminal ∘ Symbol.cell))

private def mismatchCompleted
    (s : List (symbol (Symbol A) MismatchNT)) : Prop :=
  ∃ xs ys : List A, xs.length ≠ ys.length ∧
    s = (xs.map Symbol.cell ++
      Symbol.separator :: ys.reverse.map Symbol.cell).map symbol.terminal

private def mismatchWellFormed
    (s : List (symbol (Symbol A) MismatchNT)) : Prop :=
  mismatchPairProgress s ∨ mismatchLeftProgress s ∨
    mismatchRightProgress s ∨ mismatchCompleted s

private theorem mismatch_initial_wellFormed :
    mismatchWellFormed (A := A) [symbol.nonterminal .pair] := by
  left
  exact ⟨[], [], rfl, rfl⟩

private theorem mismatch_split
    {N : Type} {left right u v : List (symbol (Symbol A) N)} {p q : N}
    (h : left ++ symbol.nonterminal q :: right =
      u ++ symbol.nonterminal p :: v)
    (hl : symbol.nonterminal p ∉ left)
    (hr : symbol.nonterminal p ∉ right) :
    left = u ∧ q = p ∧ right = v := by
  have hs := (List.append_cons_inj_of_notMem hl hr).mp h
  exact ⟨hs.1, symbol.nonterminal.inj hs.2.1, hs.2.2⟩

private theorem mismatch_pair_step
    {s t : List (symbol (Symbol A) MismatchNT)}
    (hs : mismatchPairProgress s)
    (hst : CF_transforms (mismatchGrammar (A := A)) s t) :
    mismatchWellFormed t := by
  obtain ⟨xs, ys, hlen, rfl⟩ := hs
  obtain ⟨r, u, v, hrule, hbefore, rfl⟩ := hst
  have hbefore' :
      xs.map (symbol.terminal ∘ Symbol.cell) ++
          symbol.nonterminal .pair ::
            ys.reverse.map (symbol.terminal ∘ Symbol.cell) =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [List.append_assoc] using hbefore
  obtain ⟨rfl, hrnt, rfl⟩ := mismatch_split hbefore'
    (by simp) (by simp)
  rw [mismatch_mem_rules_iff] at hrule
  rcases hrule with ⟨a, b, hr⟩ | ⟨a, hr⟩ | ⟨a, hr⟩ |
      ⟨b, hr⟩ | ⟨b, hr⟩ | hr | hr
  · subst r
    left
    refine ⟨xs ++ [a], ys ++ [b], by simp [hlen], ?_⟩
    simp [mismatchCell, List.map_append, List.reverse_append,
      List.append_assoc]
  · subst r
    right; left
    refine ⟨xs, ys, [a], hlen, by simp, ?_⟩
    simp [mismatchCell, List.map_append, List.append_assoc]
  · subst r; cases hrnt
  · subst r
    right; right; left
    refine ⟨xs, ys, [b], hlen, by simp, ?_⟩
    simp [mismatchCell, mismatchSeparator, List.append_assoc]
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r; cases hrnt

private theorem mismatch_left_step
    {s t : List (symbol (Symbol A) MismatchNT)}
    (hs : mismatchLeftProgress s)
    (hst : CF_transforms (mismatchGrammar (A := A)) s t) :
    mismatchWellFormed t := by
  obtain ⟨xs, ys, extra, hlen, hextra, rfl⟩ := hs
  obtain ⟨r, u, v, hrule, hbefore, rfl⟩ := hst
  have hbefore' :
      (xs ++ extra).map (symbol.terminal ∘ Symbol.cell) ++
          symbol.nonterminal .left ::
            ys.reverse.map (symbol.terminal ∘ Symbol.cell) =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [List.append_assoc] using hbefore
  obtain ⟨rfl, hrnt, rfl⟩ := mismatch_split hbefore'
    (by simp) (by simp)
  rw [mismatch_mem_rules_iff] at hrule
  rcases hrule with ⟨a, b, hr⟩ | ⟨a, hr⟩ | ⟨a, hr⟩ |
      ⟨b, hr⟩ | ⟨b, hr⟩ | hr | hr
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r
    right; left
    refine ⟨xs, ys, extra ++ [a], hlen, by simp [hextra], ?_⟩
    simp [mismatchCell, List.map_append, List.append_assoc]
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r
    right; right; right
    refine ⟨xs ++ extra, ys, ?_, ?_⟩
    · intro heq
      simp only [List.length_append] at heq
      have hpos : 0 < extra.length := List.length_pos_of_ne_nil hextra
      omega
    · simp [mismatchSeparator, List.map_append]
  · subst r; cases hrnt

private theorem mismatch_right_step
    {s t : List (symbol (Symbol A) MismatchNT)}
    (hs : mismatchRightProgress s)
    (hst : CF_transforms (mismatchGrammar (A := A)) s t) :
    mismatchWellFormed t := by
  obtain ⟨xs, ys, extra, hlen, hextra, rfl⟩ := hs
  obtain ⟨r, u, v, hrule, hbefore, rfl⟩ := hst
  let left : List (symbol (Symbol A) MismatchNT) :=
    xs.map (symbol.terminal ∘ Symbol.cell) ++
      mismatchSeparator :: extra.map (symbol.terminal ∘ Symbol.cell)
  have hbefore' :
      left ++ symbol.nonterminal .right ::
          ys.reverse.map (symbol.terminal ∘ Symbol.cell) =
        u ++ symbol.nonterminal r.1 :: v := by
    simpa [left, List.append_assoc] using hbefore
  obtain ⟨rfl, hrnt, rfl⟩ := mismatch_split hbefore'
    (by simp [left, mismatchSeparator]) (by simp)
  rw [mismatch_mem_rules_iff] at hrule
  rcases hrule with ⟨a, b, hr⟩ | ⟨a, hr⟩ | ⟨a, hr⟩ |
      ⟨b, hr⟩ | ⟨b, hr⟩ | hr | hr
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r; cases hrnt
  · subst r
    right; right; left
    refine ⟨xs, ys, extra ++ [b], hlen, by simp [hextra], ?_⟩
    simp [left, mismatchCell, mismatchSeparator, List.map_append,
      List.append_assoc]
  · subst r; cases hrnt
  · subst r
    right; right; right
    refine ⟨xs, ys ++ extra.reverse, ?_, ?_⟩
    · simp [hlen]
      have : 0 < extra.length := List.length_pos_of_ne_nil hextra
      omega
    · simp [left, mismatchSeparator, List.map_append,
        List.map_reverse, List.reverse_append, List.append_assoc]

private theorem mismatch_completed_no_step
    {s t : List (symbol (Symbol A) MismatchNT)}
    (hs : mismatchCompleted s) :
    ¬ CF_transforms (mismatchGrammar (A := A)) s t := by
  rintro ⟨r, u, v, -, hbefore, -⟩
  obtain ⟨xs, ys, -, rfl⟩ := hs
  have hn : symbol.nonterminal r.1 ∈
      (xs.map Symbol.cell ++
        Symbol.separator :: ys.reverse.map Symbol.cell).map symbol.terminal := by
    rw [hbefore]
    simp
  simpa using hn

private theorem mismatch_wellFormed_step
    {s t : List (symbol (Symbol A) MismatchNT)}
    (hs : mismatchWellFormed s)
    (hst : CF_transforms (mismatchGrammar (A := A)) s t) :
    mismatchWellFormed t := by
  rcases hs with hp | hl | hr | hc
  · exact mismatch_pair_step hp hst
  · exact mismatch_left_step hl hst
  · exact mismatch_right_step hr hst
  · exact (mismatch_completed_no_step hc hst).elim

private theorem mismatch_wellFormed_of_derives
    {s : List (symbol (Symbol A) MismatchNT)}
    (h : CF_derives (mismatchGrammar (A := A))
      [symbol.nonterminal .pair] s) : mismatchWellFormed s := by
  induction h with
  | refl => exact mismatch_initial_wellFormed
  | tail _ hstep ih => exact mismatch_wellFormed_step ih hstep

private theorem mismatchGrammar_sound :
    CF_language (mismatchGrammar (A := A)) ≤ lengthMismatchLanguage A := by
  intro w hw
  have hform := mismatch_wellFormed_of_derives hw
  rcases hform with hp | hl | hr | hc
  · obtain ⟨xs, ys, -, heq⟩ := hp
    have hn : symbol.nonterminal MismatchNT.pair ∈ w.map symbol.terminal := by
      rw [heq]
      simp
    simpa using hn
  · obtain ⟨xs, ys, extra, -, -, heq⟩ := hl
    have hn : symbol.nonterminal MismatchNT.left ∈ w.map symbol.terminal := by
      rw [heq]
      simp
    simpa using hn
  · obtain ⟨xs, ys, extra, -, -, heq⟩ := hr
    have hn : symbol.nonterminal MismatchNT.right ∈ w.map symbol.terminal := by
      rw [heq]
      simp
    simpa using hn
  · obtain ⟨xs, ys, hlen, heq⟩ := hc
    exact ⟨xs, ys, hlen,
      (Function.Injective.list_map fun _ _ h => symbol.terminal.inj h) heq⟩

private theorem mismatch_derive_left_tail (xs : List A) :
    CF_derives (mismatchGrammar (A := A)) [symbol.nonterminal .left]
      (xs.map (symbol.terminal ∘ Symbol.cell) ++ [mismatchSeparator]) := by
  induction xs with
  | nil =>
      apply CF_deri_of_tran
      exact ⟨(.left, [mismatchSeparator]), [], [],
        (mismatch_mem_rules_iff).2 (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl rfl)))))), rfl, rfl⟩
  | cons a xs ih =>
      apply CF_deri_of_tran_deri
      · exact ⟨(.left, [mismatchCell a, symbol.nonterminal .left]),
          [], [], (mismatch_mem_rules_iff).2
            (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))), rfl, rfl⟩
      · simpa [mismatchCell, List.append_assoc] using
          CF_deri_with_prefix [mismatchCell a] ih

private theorem mismatch_derive_right_tail (xs : List A) :
    CF_derives (mismatchGrammar (A := A)) [symbol.nonterminal .right]
      (xs.map (symbol.terminal ∘ Symbol.cell)) := by
  induction xs with
  | nil =>
      apply CF_deri_of_tran
      exact ⟨(.right, []), [], [], (mismatch_mem_rules_iff).2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
        rfl, rfl⟩
  | cons a xs ih =>
      apply CF_deri_of_tran_deri
      · exact ⟨(.right, [mismatchCell a, symbol.nonterminal .right]),
          [], [], (mismatch_mem_rules_iff).2
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))),
          rfl, rfl⟩
      · simpa [mismatchCell] using CF_deri_with_prefix [mismatchCell a] ih

private theorem mismatch_derive (xs ys : List A)
    (hne : xs.length ≠ ys.length) :
    CF_derives (mismatchGrammar (A := A)) [symbol.nonterminal .pair]
      ((xs.map Symbol.cell ++ Symbol.separator ::
        ys.reverse.map Symbol.cell).map symbol.terminal) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp at hne
      | cons b ys =>
          have htail := mismatch_derive_right_tail (A := A)
            ((b :: ys).reverse).tail
          have hnonempty : (b :: ys).reverse ≠ [] := by simp
          obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hnonempty
          have hstart : CF_derives (mismatchGrammar (A := A))
              [symbol.nonterminal .pair]
              [mismatchSeparator, mismatchCell z, symbol.nonterminal .right] := by
            apply CF_deri_of_tran
            exact ⟨(.pair, [mismatchSeparator, mismatchCell z,
                symbol.nonterminal .right]), [], [],
              (mismatch_mem_rules_iff).2 (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨z, rfl⟩)))), rfl, rfl⟩
          rw [hz] at htail ⊢
          have hrest := CF_deri_with_prefix
            [mismatchSeparator, mismatchCell z] htail
          exact CF_deri_of_deri_deri hstart (by
            simpa [mismatchCell, mismatchSeparator] using hrest)
  | cons a xs ih =>
      cases ys with
      | nil =>
          have htail := mismatch_derive_left_tail (A := A) xs
          have hstart : CF_derives (mismatchGrammar (A := A))
              [symbol.nonterminal .pair]
              [mismatchCell a, symbol.nonterminal .left] := by
            apply CF_deri_of_tran
            exact ⟨(.pair, [mismatchCell a, symbol.nonterminal .left]),
              [], [], (mismatch_mem_rules_iff).2
                (Or.inr (Or.inl ⟨a, rfl⟩)), rfl, rfl⟩
          exact CF_deri_of_deri_deri hstart (by
            simpa [mismatchCell, mismatchSeparator, List.map_append,
              List.append_assoc] using CF_deri_with_prefix [mismatchCell a] htail)
      | cons b ys =>
          have hne' : xs.length ≠ ys.length := by simpa using hne
          have hinner := ih ys hne'
          apply CF_deri_of_tran_deri
          · exact ⟨(.pair, [mismatchCell a, symbol.nonterminal .pair,
                mismatchCell b]), [], [], (mismatch_mem_rules_iff).2
              (Or.inl ⟨a, b, rfl⟩), rfl, rfl⟩
          · have hcontext := CF_deri_with_prefix_and_postfix
              [mismatchCell a] [mismatchCell b] hinner
            simpa [mismatchCell, mismatchSeparator, List.reverse_cons,
              List.map_append, List.append_assoc] using hcontext

private theorem mismatchGrammar_complete :
    lengthMismatchLanguage A ≤ CF_language (mismatchGrammar (A := A)) := by
  intro w hw
  obtain ⟨xs, ys, hne, rfl⟩ := hw
  exact mismatch_derive xs ys hne

/-- The unequal-width mirror core is context-free over every finite cell
alphabet. -/
public theorem lengthMismatchLanguage_is_CF :
    is_CF (lengthMismatchLanguage A) := by
  apply is_CF_via_cfg_implies_is_CF
  exact ⟨mismatchGrammar, Set.Subset.antisymm mismatchGrammar_sound
    mismatchGrammar_complete⟩

end Grammar

end FinitePairVerifier

/-- Namespace-level spelling of the unequal-width core. -/
public abbrev lengthMismatchLanguage (A : Type) : Language (Symbol A) :=
  FinitePairVerifier.lengthMismatchLanguage A

/-- The unequal-width core is context-free over every finite cell alphabet. -/
public theorem lengthMismatchLanguage_is_CF [Fintype A] [DecidableEq A] :
    is_CF (lengthMismatchLanguage A) :=
  FinitePairVerifier.lengthMismatchLanguage_is_CF

end ContextFree.MalformedHistories
