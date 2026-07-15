module

public import Langlib.Grammars.LR.Equivalence.CanonicalParser

/-!
# Soundness of the canonical LR parser

Every bottom-up parser step reverses either no grammar step (a shift) or one
rightmost grammar step (a reduction).  Consequently an accepting canonical
run reconstructs a derivation of its input word.
-/

@[expose]
public section

open Language

namespace CF_grammar.LRk.CanonicalParser

open CF_grammar.LRk

variable {T : Type} [Fintype T]

/-- A trusted canonical parser step reads the sentential forms backwards. -/
public theorem Step.form_derives {G : CF_grammar T} {k : ℕ}
    {c d : Config T G} (h : Step G k c d) :
    G.augment.DerivesRightmost d.form c.form := by
  cases h with
  | @shift gamma a w _ =>
      simpa [Config.form, List.append_assoc] using
        (Relation.ReflTransGen.refl :
          G.augment.DerivesRightmost
            (gamma ++ [symbol.terminal a] ++
              w.map (symbol.terminal (N := G.augment.nt)))
            (gamma ++ [symbol.terminal a] ++
              w.map (symbol.terminal (N := G.augment.nt))))
  | @reduce gamma p w r _ hgamma =>
      apply Relation.ReflTransGen.single
      refine ⟨ruleAt G.augment r, ruleAt_mem G.augment r,
        p, w, ?_, ?_⟩
      · rfl
      · simp [Config.form, hgamma, List.append_assoc]

/-- Along a canonical run, the current sentential form rightmost-derives the
sentential form at the beginning of the run. -/
public theorem Reaches.form_derives {G : CF_grammar T} {k : ℕ}
    {c d : Config T G} (h : Reaches G k c d) :
    G.augment.DerivesRightmost d.form c.form := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Step.form_derives hstep).trans ih

/-- Every word accepted by the canonical table belongs to the source
context-free language. -/
public theorem accepts_sound (G : CF_grammar T) (k : ℕ) {w : List T}
    (h : Accepts G k w) : w ∈ CF_language G := by
  rcases h with ⟨c, hreach, hinput, haccept⟩
  rcases c with ⟨gamma, input⟩
  change input = [] at hinput
  subst input
  change tableAction G k (scanKernel G k gamma)
    (eofLookahead T k) = .accept at haccept
  obtain ⟨i, hi, hirule⟩ :=
    (tableAction_accept_iff G k (scanKernel G k gamma)
      (eofLookahead T k)).mp haccept
  have hcand := reductionItem?_reductionCandidate G k hi
  rw [hirule, ruleAt_startRuleIndex] at hcand
  rcases hcand with ⟨_, p, s, hpre, hgamma, _⟩
  have hroot : p = [] ∧ s = [] :=
    fresh_prehandle_eq_root G (by
      simpa [CF_grammar.augmentStartRule] using hpre)
  rcases hroot with ⟨rfl, rfl⟩
  have hgamma' :
      gamma = [symbol.nonterminal (some G.initial)] := by
    simpa [CF_grammar.augmentStartRule] using hgamma
  subst gamma
  have hder := Reaches.form_derives hreach
  have hder' : G.augment.DerivesRightmost
      [symbol.nonterminal (some G.initial)]
      (w.map (symbol.terminal (N := G.augment.nt))) := by
    simpa [Config.form, initialConfig] using hder
  have hfull : G.augment.DerivesRightmost
      [symbol.nonterminal G.augment.initial]
      (w.map (symbol.terminal (N := G.augment.nt))) :=
    (Relation.ReflTransGen.single
      (CF_grammar.augment_start_producesRightmost G)).trans hder'
  rw [← G.augment_language]
  exact CF_grammar.derives_of_derivesRightmost hfull

end CF_grammar.LRk.CanonicalParser
