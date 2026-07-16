module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.HeadPairs
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineEdges

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem parentPrefix_eq_nil_of_introduces_start
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : Introduces M childPrefix child childSuffix
      parentPrefix PDA_to_CFG.N.start rule) :
    parentPrefix = [] := by
  rcases h with ⟨alpha, beta, t, z, hparent, _⟩
  exact (hparent.start_eq_nil M).1

public theorem activeHeadUnique_of_epsilonIntroducingHeadsUnique
    (M : DPDA Q T S) (hepsilon : EpsilonIntroducingHeadsUnique M) :
    ActiveHeadUnique M := by
  intro childPrefix child suffix₁ suffix₂
    parentPrefix₁ parentPrefix₂ parent₁ parent₂ rule₁ rule₂
    hlist h₁ h₂ hlook
  have hepsilonCase := hepsilon childPrefix child suffix₁ suffix₂
    parentPrefix₁ parentPrefix₂ parent₁ parent₂ rule₁ rule₂
    hlist h₁ h₂ hlook
  have hv₁ := listIntroduction_of_introduces M hlist h₁
  have hv₂ := listIntroduction_of_introduces M hlist h₂
  generalize hprefix : childPrefix = childPrefix₂ at hv₂
  generalize hchild : child = child₂ at hv₂
  cases hv₁ <;> cases hv₂ <;> simp only [activeDescriptor]
  case read.read htransition₁ hrule₁ hparent₁
      q₂ target₂ next₂ a₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    obtain ⟨hparentPrefix, haSymbol⟩ :=
      append_singleton_injective hprefix
    have ha := symbol.terminal.inj haSymbol
    subst parentPrefix₂
    subst a₂
    obtain ⟨hq, hZ⟩ := activeSingle_read_heads_unique M
      hparent₁ hparent₂ htransition₁ htransition₂ hrule₁
    simp [hq, hZ]
  case read.epsilon q₂ target₂ next₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    exact hepsilonCase (Or.inr
      ⟨q₂, target₂, next₂, Z₂, gamma₂, htransition₂, rfl⟩)
  case epsilon.read htransition₁ hrule₁ hparent₁
      q₂ target₂ next₂ a₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    exact hepsilonCase (Or.inl
      ⟨_, _, _, _, _, htransition₁, rfl⟩)
  case epsilon.epsilon htransition₁ hrule₁ hparent₁
      q₂ target₂ next₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    exact hepsilonCase (Or.inl
      ⟨_, _, _, _, _, htransition₁, rfl⟩)
  case epsilon.split htransition₁ hrule₁ hparent₁
      q₂ middle₂ target₂ Z₂ gamma₂
      hparent₂ hlength₂ hrule₂ =>
    exact hepsilonCase (Or.inl
      ⟨_, _, _, _, _, htransition₁, rfl⟩)
  case epsilon.start htransition₁ hrule₁ hparent₁
      target₂ hparent₂ hrule₂ =>
    exact hepsilonCase (Or.inl
      ⟨_, _, _, _, _, htransition₁, rfl⟩)
  case split.epsilon q₂ target₂ next₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    exact hepsilonCase (Or.inr
      ⟨q₂, target₂, next₂, Z₂, gamma₂, htransition₂, rfl⟩)
  case start.epsilon q₂ target₂ next₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    exact hepsilonCase (Or.inr
      ⟨q₂, target₂, next₂, Z₂, gamma₂, htransition₂, rfl⟩)
  case read.split =>
    obtain ⟨_, hlast⟩ := append_singleton_injective hprefix
    cases hlast
  case split.read =>
    obtain ⟨_, hlast⟩ := append_singleton_injective hprefix
    cases hlast
  case read.start =>
    have hp₂ := parentPrefix_eq_nil_of_introduces_start M h₂
    rw [hp₂] at hprefix
    simp at hprefix
  case split.start =>
    have hp₂ := parentPrefix_eq_nil_of_introduces_start M h₂
    rw [hp₂] at hprefix
    simp at hprefix
  case start.read =>
    have hp₁ := parentPrefix_eq_nil_of_introduces_start M h₁
    rw [hp₁] at hprefix
    simp at hprefix
  case start.split =>
    have hp₁ := parentPrefix_eq_nil_of_introduces_start M h₁
    rw [hp₁] at hprefix
    simp at hprefix
  case split.split =>
    obtain ⟨_, hlast⟩ := append_singleton_injective hprefix
    have hsingle := symbol.nonterminal.inj hlast
    injection hsingle with hq hZ hmiddle
    simp [hq, hZ]

end


end DPDA_to_LR
