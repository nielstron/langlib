module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Introductions

/-!
# Operational interpretation of active characteristic spines

`ActiveSpine` remembers the partial-tree ancestry of a rightmost-reachable
nonterminal.  For the LR argument we also need to know how a chosen terminal
completion of the visible prefix is divided among the edges of that ancestry.
`OperationalSpine` records precisely that extra information.  In particular,
it retains an operational `Focused` cut at every ancestor rather than only at
the final active node.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- An active derivation spine equipped with a concrete terminal completion
of every prefix on the root-to-active path. -/
public inductive OperationalSpine (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M →
      List T → List T → Prop
  | root : OperationalSpine M [] (characteristicGrammar M).initial [] []
  | descend
      {p₀ alpha beta : List (symbol T (Nonterminal M))}
      {parent child : Nonterminal M} {t z preWord leftWord : List T}
      {r : Nonterminal M × List (symbol T (Nonterminal M))}
      (parentSpine : OperationalSpine M p₀ parent t preWord)
      (hr : r ∈ (characteristicGrammar M).rules)
      (hlhs : r.1 = parent)
      (hrhs : r.2 = alpha ++ [symbol.nonterminal child] ++ beta)
      (halpha : (characteristicGrammar M).DerivesRightmost
        alpha (leftWord.map symbol.terminal))
      (hbeta : (characteristicGrammar M).DerivesRightmost
        beta (z.map symbol.terminal)) :
      OperationalSpine M (p₀ ++ alpha) child (z ++ t)
        (preWord ++ leftWord)

/-- Forgetting terminal-completion data recovers the underlying ancestry. -/
public theorem OperationalSpine.activeSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {s preWord : List T} (h : OperationalSpine M p A s preWord) :
    ActiveSpine M p A s := by
  induction h with
  | root => exact ActiveSpine.root
  | descend parentSpine hr hlhs hrhs halpha hbeta ih =>
      exact ActiveSpine.descend ih hr hlhs hrhs hbeta

/-- The last index really is a terminal rightmost completion of the visible
prefix. -/
public theorem OperationalSpine.prefixDerives (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {s preWord : List T} (h : OperationalSpine M p A s preWord) :
    (characteristicGrammar M).DerivesRightmost p
      (preWord.map symbol.terminal) := by
  induction h with
  | root => exact Relation.ReflTransGen.refl
  | descend parentSpine hr hlhs hrhs halpha hbeta ih =>
      exact ih.append_to_terminals halpha

/-- The operational meaning of the final active occurrence, with the exact
prefix word accumulated by the spine. -/
public theorem OperationalSpine.focused (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {s preWord : List T} (h : OperationalSpine M p A s preWord) :
    Focused M A preWord s := by
  exact focused_of_prehandle M (h.activeSpine M |>.derivesRightmost M)
    (h.prefixDerives M)

/-- Equip an ancestry spine with any concrete terminal completion of its
visible prefix.  The append-splitting theorem makes every edge yield explicit.
-/
public theorem operationalSpine_of_activeSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {s preWord : List T} (hspine : ActiveSpine M p A s)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (preWord.map symbol.terminal)) :
    OperationalSpine M p A s preWord := by
  induction hspine generalizing preWord with
  | root =>
      have hterminal : (preWord.map
          (symbol.terminal (N := Nonterminal M))) = [] :=
        CF_grammar.DerivesRightmost.eq_of_map_terminal_source
          (G := characteristicGrammar M) (w := []) hp
      have hnil : preWord = [] := by simpa using congrArg List.length hterminal
      subst preWord
      exact OperationalSpine.root
  | @descend p₀ alpha beta parent child t z r parentSpine hr hlhs hrhs
      hbeta ih =>
      obtain ⟨parentWord, leftWord, hword, hparent, halpha⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      subst preWord
      exact OperationalSpine.descend (ih hparent) hr hlhs hrhs halpha hbeta

/-- Direct operational interpretation of a reachable prehandle and a chosen
terminal completion of its prefix. -/
public theorem operationalSpine_of_prehandle (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {s preWord : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal))
    (hp : (characteristicGrammar M).DerivesRightmost p
      (preWord.map symbol.terminal)) :
    OperationalSpine M p A s preWord :=
  operationalSpine_of_activeSpine M (activeSpine_of_derivesRightmost M h) hp

end

end DPDA_to_LR
