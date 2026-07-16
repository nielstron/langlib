module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ActiveSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CoreEasy

/-!
# Introducing edges in an active characteristic spine

This file gives the top-edge interface used by the LR-core proof.  It exposes
the parent handle and retained production which introduced a displayed active
child, while hiding the auxiliary decomposition witnesses of `ActiveSpine`.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A concrete retained production is the final edge of an active derivation
spine.  The indices record both the visible child prehandle and its parent
prehandle. -/
@[expose]
public def Introduces (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (child : Nonterminal M) (childSuffix : List T)
    (parentPrefix : List (symbol T (Nonterminal M)))
    (parent : Nonterminal M)
    (rule : Nonterminal M × List (symbol T (Nonterminal M))) : Prop :=
  ∃ (alpha beta : List (symbol T (Nonterminal M))) (t z : List T),
    ActiveSpine M parentPrefix parent t ∧
    rule ∈ (characteristicGrammar M).rules ∧
    rule.1 = parent ∧
    rule.2 = alpha ++ [symbol.nonterminal child] ++ beta ∧
    (characteristicGrammar M).DerivesRightmost
      beta (z.map symbol.terminal) ∧
    childPrefix = parentPrefix ++ alpha ∧
    childSuffix = z ++ t

/-- Direct constructor for an introducing edge. -/
public theorem Introduces.of_descend (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    {alpha beta : List (symbol T (Nonterminal M))} {t z : List T}
    (hparent : ActiveSpine M parentPrefix parent t)
    (hrule : rule ∈ (characteristicGrammar M).rules)
    (hlhs : rule.1 = parent)
    (hrhs : rule.2 = alpha ++ [symbol.nonterminal child] ++ beta)
    (hbeta : (characteristicGrammar M).DerivesRightmost
      beta (z.map symbol.terminal))
    (hprefix : childPrefix = parentPrefix ++ alpha)
    (hsuffix : childSuffix = z ++ t) :
    Introduces M childPrefix child childSuffix
      parentPrefix parent rule := by
  exact ⟨alpha, beta, t, z, hparent, hrule, hlhs, hrhs, hbeta,
    hprefix, hsuffix⟩

/-- Applying a nonbase rule whose last symbol is `child` adds an introducing
edge with unchanged terminal suffix. -/
public theorem Introduces.finalChild (M : DPDA Q T S)
    {parentPrefix action : List (symbol T (Nonterminal M))}
    {parent child : Nonterminal M} {suffix : List T}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (hparent : ActiveSpine M parentPrefix parent suffix)
    (hrule : rule ∈ (characteristicGrammar M).rules)
    (hlhs : rule.1 = parent)
    (hrhs : rule.2 = action ++ [symbol.nonterminal child]) :
    Introduces M (parentPrefix ++ action) child suffix
      parentPrefix parent rule := by
  apply Introduces.of_descend M hparent hrule hlhs
      (beta := []) (z := [])
  · simpa using hrhs
  · exact Relation.ReflTransGen.refl
  · rfl
  · rfl

/-- The introducing-edge witness itself reconstructs the visible child
spine. -/
public theorem Introduces.activeSpine (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : Introduces M childPrefix child childSuffix
      parentPrefix parent rule) :
    ActiveSpine M childPrefix child childSuffix := by
  rcases h with ⟨alpha, beta, t, z, hparent, hrule, hlhs, hrhs,
    hbeta, hprefix, hsuffix⟩
  rw [hprefix, hsuffix]
  exact ActiveSpine.descend hparent hrule hlhs hrhs hbeta

/-- The semantic top-edge property needed by the nonbase LR-core cases: one
visible active child and one symbol of following input determine its parent
handle and the production which introduced it. -/
@[expose]
public def IntroducingEdgesUnique (M : DPDA Q T S) : Prop :=
  ∀ (childPrefix : List (symbol T (Nonterminal M)))
      (child : Nonterminal M) (suffix₁ suffix₂ : List T)
      (parentPrefix₁ parentPrefix₂ :
        List (symbol T (Nonterminal M)))
      (parent₁ parent₂ : Nonterminal M)
      (rule₁ rule₂ :
        Nonterminal M × List (symbol T (Nonterminal M))),
    IsListSymbol M (symbol.nonterminal child) →
    Introduces M childPrefix child suffix₁
        parentPrefix₁ parent₁ rule₁ →
    Introduces M childPrefix child suffix₂
        parentPrefix₂ parent₂ rule₂ →
    suffix₁.take 1 = suffix₂.take 1 →
    parentPrefix₁ = parentPrefix₂ ∧ rule₁ = rule₂

/-- Once top-edge uniqueness is available, all nonbase handle comparisons
reduce uniformly to cancellation of their final characteristic-list marker. -/
public theorem nonbase_collision_of_introducingEdgesUnique
    (M : DPDA Q T S) (hedges : IntroducingEdgesUnique M)
    {r₁ r₂ : Nonterminal M × List (symbol T (Nonterminal M))}
    (hr₁ : r₁ ∈ (characteristicGrammar M).rules)
    (hr₂ : r₂ ∈ (characteristicGrammar M).rules)
    {p₁ p₂ action₁ action₂ :
      List (symbol T (Nonterminal M))}
    {s₁ s₂ y : List T}
    {q₁ q₂ target₁ target₂ : State M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (hspine₁ : ActiveSpine M p₁ r₁.1 s₁)
    (hspine₂ : ActiveSpine M p₂ r₂.1 s₂)
    (hrhs₁ : r₁.2 = action₁ ++
      [symbol.nonterminal
        (PDA_to_CFG.N.list q₁ gamma₁ target₁)])
    (hrhs₂ : r₂.2 = action₂ ++
      [symbol.nonterminal
        (PDA_to_CFG.N.list q₂ gamma₂ target₂)])
    (hleft₁ : ∀ X ∈ p₁ ++ action₁, ¬ IsListSymbol M X)
    (hleft₂ : ∀ X ∈ p₂ ++ action₂, ¬ IsListSymbol M X)
    (hform : p₂ ++ r₂.2 ++ s₂.map symbol.terminal =
      p₁ ++ r₁.2 ++ y.map symbol.terminal)
    (hlook : s₁.take 1 = y.take 1) :
    p₁ = p₂ ∧ r₁ = r₂ := by
  have hform' :
      (p₂ ++ action₂) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list q₂ gamma₂ target₂)] ++
          s₂.map symbol.terminal =
        (p₁ ++ action₁) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list q₁ gamma₁ target₁)] ++
          y.map symbol.terminal := by
    rw [hrhs₁, hrhs₂] at hform
    simpa [List.append_assoc] using hform
  obtain ⟨haction, hq, hgamma, htarget, hsuffix⟩ :=
    cancel_characteristic_list_marker M hleft₁ hleft₂ hform'
  have hi₁ : Introduces M (p₁ ++ action₁)
      (PDA_to_CFG.N.list q₁ gamma₁ target₁) s₁
      p₁ r₁.1 r₁ :=
    Introduces.finalChild M hspine₁ hr₁ rfl hrhs₁
  have hi₂ : Introduces M (p₂ ++ action₂)
      (PDA_to_CFG.N.list q₂ gamma₂ target₂) s₂
      p₂ r₂.1 r₂ :=
    Introduces.finalChild M hspine₂ hr₂ rfl hrhs₂
  rw [haction, hq, hgamma, htarget, hsuffix] at hi₂
  exact hedges _ _ _ _ _ _ _ _ _ _
    (isListSymbol_list M q₁ target₁ gamma₁) hi₁ hi₂ hlook

end

end DPDA_to_LR
