module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Rules

/-!
# Fresh-start bookkeeping for the DPDA characteristic grammar

The ordinary characteristic-grammar argument proves Knuth's condition for the
grammar itself.  `CF_grammar.IsLRk`, however, deliberately checks the grammar
after adjoining one more fresh start symbol.  This file discharges the extra
start/start and start/ordinary cases.  In particular, the wrapper below does
not silently omit accept/reduce or accept/shift conflicts.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type}

/-! ## A generic no-reintroduction invariant -/

private theorem ProducesRightmost.avoids_of_avoids
    {G : CF_grammar T} {A : G.nt}
    (hrhs : ∀ r ∈ G.rules, symbol.nonterminal A ∉ r.2)
    {u v : List (symbol T G.nt)}
    (hu : symbol.nonterminal A ∉ u)
    (h : G.ProducesRightmost u v) :
    symbol.nonterminal A ∉ v := by
  rcases h with ⟨r, hr, p, s, hsource, htarget⟩
  rw [htarget]
  intro hmem
  simp only [List.mem_append] at hmem
  rcases hmem with (hp | hrhs') | hs
  · apply hu
    rw [hsource]
    simp [hp]
  · exact hrhs r hr hrhs'
  · simpa using hs

private theorem ProducesRightmost.avoids_of_initial
    {G : CF_grammar T}
    (hrhs : ∀ r ∈ G.rules,
      symbol.nonterminal G.initial ∉ r.2)
    {v : List (symbol T G.nt)}
    (h : G.ProducesRightmost [symbol.nonterminal G.initial] v) :
    symbol.nonterminal G.initial ∉ v := by
  rcases h with ⟨r, hr, p, s, hsource, htarget⟩
  have hlen := congrArg List.length hsource
  simp only [List.length_singleton, List.length_append, List.length_map] at hlen
  have hpLen : p.length = 0 := by omega
  have hsLen : s.length = 0 := by omega
  have hp : p = [] := List.length_eq_zero_iff.mp hpLen
  have hs : s = [] := List.length_eq_zero_iff.mp hsLen
  rw [htarget, hp, hs]
  simpa using hrhs r hr

/-- If no production reintroduces the initial nonterminal, a rightmost
derivation from it is either still reflexive or has eliminated it forever. -/
private theorem derivesRightmost_initial_or_avoids
    {G : CF_grammar T}
    (hrhs : ∀ r ∈ G.rules,
      symbol.nonterminal G.initial ∉ r.2)
    {v : List (symbol T G.nt)}
    (h : G.DerivesRightmost [symbol.nonterminal G.initial] v) :
    v = [symbol.nonterminal G.initial] ∨
      symbol.nonterminal G.initial ∉ v := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      right
      rcases ih with hstill | hav
      · rw [hstill] at hstep
        exact ProducesRightmost.avoids_of_initial hrhs hstep
      · exact ProducesRightmost.avoids_of_avoids hrhs hav hstep

/-! ## The outer augmentation is genuinely fresh -/

private theorem none_not_mem_augmentString (G : CF_grammar T)
    (w : List (symbol T G.nt)) :
    symbol.nonterminal none ∉ CF_grammar.augmentString w := by
  intro hmem
  simp only [CF_grammar.augmentString, List.mem_map] at hmem
  rcases hmem with ⟨a, _, ha⟩
  cases a <;> simp [CF_grammar.augmentSymbol] at ha

private theorem augment_rule_rhs_avoids (G : CF_grammar T)
    (r : G.augment.nt × List (symbol T G.augment.nt))
    (hr : r ∈ G.augment.rules) :
    symbol.nonterminal G.augment.initial ∉ r.2 := by
  rcases List.mem_cons.mp hr with hstart | hmapped
  · subst r
    change symbol.nonterminal none ∉
      [symbol.nonterminal (some G.initial)]
    intro hmem
    have heq := symbol.nonterminal.inj (List.mem_singleton.mp hmem)
    cases heq
  · rcases List.mem_map.mp hmapped with ⟨r₀, _, rfl⟩
    exact none_not_mem_augmentString G r₀.2

private theorem augmentString_project_of_avoids (G : CF_grammar T)
    {w : List (symbol T G.augment.nt)}
    (hw : symbol.nonterminal G.augment.initial ∉ w) :
    CF_grammar.augmentString (G.projectAugmentString w) = w := by
  change symbol.nonterminal none ∉ w at hw
  induction w with
  | nil => rfl
  | cons a w ih =>
      have ha : a ≠ symbol.nonterminal none := by
        intro heq
        apply hw
        rw [heq]
        exact List.mem_cons_self
      have htail : symbol.nonterminal none ∉ w := by
        intro hmem
        exact hw (List.mem_cons_of_mem a hmem)
      cases a with
      | terminal t =>
          change symbol.terminal t ::
              CF_grammar.augmentString (G.projectAugmentString w) =
            symbol.terminal t :: w
          rw [ih htail]
          rfl
      | nonterminal A =>
          cases A with
          | none => exact False.elim (ha rfl)
          | some A =>
              change symbol.nonterminal (some A) ::
                  CF_grammar.augmentString (G.projectAugmentString w) =
                symbol.nonterminal (some A) :: w
              rw [ih htail]

private theorem projectAugmentString_injective_of_avoids (G : CF_grammar T)
    {u v : List (symbol T G.augment.nt)}
    (hu : symbol.nonterminal G.augment.initial ∉ u)
    (hv : symbol.nonterminal G.augment.initial ∉ v)
    (h : G.projectAugmentString u = G.projectAugmentString v) :
    u = v := by
  rw [← augmentString_project_of_avoids G hu,
    ← augmentString_project_of_avoids G hv, h]

@[simp]
private theorem projectAugmentString_initial (G : CF_grammar T) :
    G.projectAugmentString
        [symbol.nonterminal (none : Option G.nt)] =
      [symbol.nonterminal G.initial] := by
  rfl

@[simp]
private theorem projectAugmentString_prehandle (G : CF_grammar T)
    (A : G.nt)
    (p : List (symbol T (Option G.nt))) (s : List T) :
    G.projectAugmentString
        (p ++ [symbol.nonterminal (some A)] ++
          s.map (symbol.terminal (N := Option G.nt))) =
      G.projectAugmentString p ++ [symbol.nonterminal A] ++
        s.map (symbol.terminal (N := G.nt)) := by
  rw [G.projectAugmentString_append, G.projectAugmentString_append,
    G.projectAugmentString_map_terminal]
  rfl

@[simp]
private theorem projectAugmentString_post (G : CF_grammar T)
    (rhs : List (symbol T G.nt))
    (p : List (symbol T (Option G.nt))) (s : List T) :
    G.projectAugmentString
        (p ++ CF_grammar.augmentString rhs ++
          s.map (symbol.terminal (N := Option G.nt))) =
      G.projectAugmentString p ++ rhs ++
        s.map (symbol.terminal (N := G.nt)) := by
  change G.projectAugmentString
      (p ++ CF_grammar.augmentString rhs ++
        s.map (symbol.terminal (N := Option G.nt))) = _
  rw [G.projectAugmentString_append, G.projectAugmentString_append,
    G.projectAugmentString_augmentString,
    G.projectAugmentString_map_terminal]

private theorem prefix_avoids_of_prehandle_avoids
    {G : CF_grammar T} {A : G.nt}
    {p : List (symbol T G.nt)} {B : G.nt} {s : List T}
    (h : symbol.nonterminal A ∉
      (p ++ [symbol.nonterminal B] ++ s.map symbol.terminal)) :
    symbol.nonterminal A ∉ p := by
  intro hp
  apply h
  simp [hp]

private theorem mapped_prehandle_ne_initial (G : CF_grammar T)
    (R : G.nt × List (symbol T G.nt))
    (p : List (symbol T (Option G.nt))) (s : List T) :
    p ++ [symbol.nonterminal (CF_grammar.augmentRule R).1] ++
        s.map symbol.terminal ≠
      [symbol.nonterminal G.augment.initial] := by
  intro h
  have hmem :
      symbol.nonterminal (T := T) (CF_grammar.augmentRule R).1 ∈
        [symbol.nonterminal (T := T) G.augment.initial] := by
    rw [← h]
    exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _))
  have heq := symbol.nonterminal.inj (List.mem_singleton.mp hmem)
  change some R.1 = none at heq
  cases heq

/-! ## The characteristic start symbol is not reintroduced -/

variable [Fintype Q] [Fintype T] [Fintype S]

private theorem characteristic_rule_rhs_avoids_initial (M : DPDA Q T S)
    (r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt))
    (hr : r ∈ (characteristicGrammar M).rules) :
    symbol.nonterminal (characteristicGrammar M).initial ∉ r.2 := by
  rw [characteristicGrammar_initial]
  rcases characteristicGrammar_rule_shape M hr with
    h | h | h | h | h
  · rcases h with ⟨q, rfl⟩
    exact List.not_mem_nil
  · rcases h with ⟨q, p, q', a, Z, alpha, _, rfl⟩
    intro hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · cases hhead
    · have heq := symbol.nonterminal.inj (List.mem_singleton.mp htail)
      cases heq
  · rcases h with ⟨q, p, q', Z, alpha, _, rfl⟩
    intro hmem
    have heq := symbol.nonterminal.inj (List.mem_singleton.mp hmem)
    cases heq
  · rcases h with ⟨q, q', p, Z, alpha, _, rfl⟩
    intro hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · have heq := symbol.nonterminal.inj hhead
      cases heq
    · have heq := symbol.nonterminal.inj (List.mem_singleton.mp htail)
      cases heq
  · rcases h with ⟨p, rfl⟩
    intro hmem
    have heq := symbol.nonterminal.inj (List.mem_singleton.mp hmem)
    cases heq

private theorem characteristic_post_avoids_initial (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (characteristicGrammar M).nt)} {s : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal)) :
    symbol.nonterminal (characteristicGrammar M).initial ∉
      (p ++ r.2 ++ s.map symbol.terminal) := by
  have hinvariant := derivesRightmost_initial_or_avoids
    (fun rule hRule => characteristic_rule_rhs_avoids_initial M rule hRule)
    hderive
  rcases hinvariant with hstill | hfree
  · have hp : p = [] := by
      have hlen := congrArg List.length hstill
      simp only [List.length_append, List.length_singleton,
        List.length_map] at hlen
      apply List.length_eq_zero_iff.mp
      omega
    have hs : s = [] := by
      have hlen := congrArg List.length hstill
      simp only [List.length_append, List.length_singleton,
        List.length_map] at hlen
      apply List.length_eq_zero_iff.mp
      omega
    have hrInitial : r.1 = (characteristicGrammar M).initial := by
      rw [hp, hs] at hstill
      change [symbol.nonterminal r.1] =
        [symbol.nonterminal (characteristicGrammar M).initial] at hstill
      exact symbol.nonterminal.inj (List.cons.inj hstill).1
    rw [hp, hs]
    intro hmem
    rw [List.map_nil, List.append_nil, List.nil_append] at hmem
    exact characteristic_rule_rhs_avoids_initial M r hr hmem
  · have hpFree : symbol.nonterminal (characteristicGrammar M).initial ∉ p :=
      prefix_avoids_of_prehandle_avoids hfree
    intro hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (hp | hrhs) | hs
    · exact hpFree hp
    · exact characteristic_rule_rhs_avoids_initial M r hr hrhs
    · rcases List.mem_map.mp hs with ⟨a, _, ha⟩
      cases ha

private theorem initial_prehandle_prefix_nil
    {G : CF_grammar T}
    (hrhs : ∀ r ∈ G.rules,
      symbol.nonterminal G.initial ∉ r.2)
    {p : List (symbol T G.nt)} {s : List T}
    (h : G.DerivesRightmost [symbol.nonterminal G.initial]
      (p ++ [symbol.nonterminal G.initial] ++ s.map symbol.terminal)) :
    p = [] := by
  rcases derivesRightmost_initial_or_avoids hrhs h with hstill | hfree
  · have hlen := congrArg List.length hstill
    simp only [List.length_append, List.length_singleton, List.length_map] at hlen
    apply List.length_eq_zero_iff.mp
    omega
  · exfalso
    apply hfree
    simp

/-! ## Adding the outer fresh start preserves LR(1) here -/

/-- For the reduced characteristic grammar, ordinary LR(1) handle uniqueness
already implies the repository's augmented `IsLRk 1` predicate. -/
public theorem characteristic_isLR1_of_core (M : DPDA Q T S)
    (hcore : (characteristicGrammar M).CoreIsLRk 1) :
    (characteristicGrammar M).IsLRk 1 := by
  let G := characteristicGrammar M
  change G.augment.CoreIsLRk 1
  unfold CF_grammar.augment
  intro r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
  let p₁' : List (symbol T (Option G.nt)) := p₁
  let p₂' : List (symbol T (Option G.nt)) := p₂
  rcases List.mem_cons.mp hr₁ with hstart₁ | hmapped₁ <;>
    rcases List.mem_cons.mp hr₂ with hstart₂ | hmapped₂
  · subst r₁
    subst r₂
    have hp₁ : p₁ = [] := initial_prehandle_prefix_nil
      (fun rule hRule => augment_rule_rhs_avoids G rule hRule) hd₁
    have hp₂ : p₂ = [] := initial_prehandle_prefix_nil
      (fun rule hRule => augment_rule_rhs_avoids G rule hRule) hd₂
    exact ⟨hp₁.trans hp₂.symm, rfl⟩
  · subst r₁
    rcases List.mem_map.mp hmapped₂ with ⟨R₂, hR₂, rfl⟩
    have : False := by
      have hd₂' : G.DerivesRightmost [symbol.nonterminal G.initial]
          (G.projectAugmentString p₂' ++ [symbol.nonterminal R₂.1] ++
            s₂.map symbol.terminal) := by
        have h := G.derivesRightmost_project_augment hd₂
        change G.DerivesRightmost
          (G.projectAugmentString
            [symbol.nonterminal (none : Option G.nt)])
          (G.projectAugmentString
            (p₂' ++ [symbol.nonterminal (some R₂.1)] ++
              s₂.map (symbol.terminal (N := Option G.nt)))) at h
        rw [projectAugmentString_initial G,
          projectAugmentString_prehandle G R₂.1 p₂' s₂] at h
        exact h
      have hpostFree := characteristic_post_avoids_initial M hR₂ hd₂'
      change symbol.nonterminal G.initial ∉
        (G.projectAugmentString p₂' ++ R₂.2 ++
          s₂.map symbol.terminal) at hpostFree
      apply hpostFree
      have hproject := congrArg G.projectAugmentString hform
      have hproject' :
          G.projectAugmentString p₂' ++ R₂.2 ++ s₂.map symbol.terminal =
            G.projectAugmentString p₁' ++ [symbol.nonterminal G.initial] ++
              y.map symbol.terminal := by
        change
          G.projectAugmentString
              (p₂' ++ CF_grammar.augmentString R₂.2 ++
                s₂.map (symbol.terminal (N := Option G.nt))) =
            G.projectAugmentString
              (p₁' ++ [symbol.nonterminal (some G.initial)] ++
                y.map (symbol.terminal (N := Option G.nt))) at hproject
        rw [projectAugmentString_post G R₂.2 p₂' s₂,
          projectAugmentString_prehandle G G.initial p₁' y] at hproject
        exact hproject
      rw [hproject']
      exact List.mem_append_left _
        (List.mem_append_right _ List.mem_cons_self)
    contradiction
  · subst r₂
    rcases List.mem_map.mp hmapped₁ with ⟨R₁, hR₁, rfl⟩
    have : False := by
      have hd₁' : G.DerivesRightmost [symbol.nonterminal G.initial]
          (G.projectAugmentString p₁' ++ [symbol.nonterminal R₁.1] ++
            s₁.map symbol.terminal) := by
        have h := G.derivesRightmost_project_augment hd₁
        change G.DerivesRightmost
          (G.projectAugmentString
            [symbol.nonterminal (none : Option G.nt)])
          (G.projectAugmentString
            (p₁' ++ [symbol.nonterminal (some R₁.1)] ++
              s₁.map (symbol.terminal (N := Option G.nt)))) at h
        rw [projectAugmentString_initial G,
          projectAugmentString_prehandle G R₁.1 p₁' s₁] at h
        exact h
      have hpostFree := characteristic_post_avoids_initial M hR₁ hd₁'
      change symbol.nonterminal G.initial ∉
        (G.projectAugmentString p₁' ++ R₁.2 ++
          s₁.map symbol.terminal) at hpostFree
      have hproject := congrArg G.projectAugmentString hform
      have hproject' :
          G.projectAugmentString p₂' ++ [symbol.nonterminal G.initial] ++
              s₂.map symbol.terminal =
            G.projectAugmentString p₁' ++ R₁.2 ++
              y.map symbol.terminal := by
        change
          G.projectAugmentString
              (p₂' ++ [symbol.nonterminal (some G.initial)] ++
                s₂.map (symbol.terminal (N := Option G.nt))) =
            G.projectAugmentString
              (p₁' ++ CF_grammar.augmentString R₁.2 ++
                y.map (symbol.terminal (N := Option G.nt))) at hproject
        rw [projectAugmentString_prehandle G G.initial p₂' s₂,
          projectAugmentString_post G R₁.2 p₁' y] at hproject
        exact hproject
      have hmem : symbol.nonterminal G.initial ∈
          G.projectAugmentString p₁' ++ R₁.2 ++
            y.map symbol.terminal := by
        rw [← hproject']
        exact List.mem_append_left _
          (List.mem_append_right _ List.mem_cons_self)
      simp only [List.mem_append] at hmem
      rcases hmem with hbase | hterminal
      · apply hpostFree
        simp only [List.mem_append]
        exact Or.inl hbase
      · simpa using hterminal
    contradiction
  · rcases List.mem_map.mp hmapped₁ with ⟨R₁, hR₁, rfl⟩
    rcases List.mem_map.mp hmapped₂ with ⟨R₂, hR₂, rfl⟩
    have hd₁' : G.DerivesRightmost [symbol.nonterminal G.initial]
        (G.projectAugmentString p₁' ++ [symbol.nonterminal R₁.1] ++
          s₁.map symbol.terminal) := by
      have h := G.derivesRightmost_project_augment hd₁
      change G.DerivesRightmost
        (G.projectAugmentString
          [symbol.nonterminal (none : Option G.nt)])
        (G.projectAugmentString
          (p₁' ++ [symbol.nonterminal (some R₁.1)] ++
            s₁.map (symbol.terminal (N := Option G.nt)))) at h
      rw [projectAugmentString_initial G,
        projectAugmentString_prehandle G R₁.1 p₁' s₁] at h
      exact h
    have hd₂' : G.DerivesRightmost [symbol.nonterminal G.initial]
        (G.projectAugmentString p₂' ++ [symbol.nonterminal R₂.1] ++
          s₂.map symbol.terminal) := by
      have h := G.derivesRightmost_project_augment hd₂
      change G.DerivesRightmost
        (G.projectAugmentString
          [symbol.nonterminal (none : Option G.nt)])
        (G.projectAugmentString
          (p₂' ++ [symbol.nonterminal (some R₂.1)] ++
            s₂.map (symbol.terminal (N := Option G.nt)))) at h
      rw [projectAugmentString_initial G,
        projectAugmentString_prehandle G R₂.1 p₂' s₂] at h
      exact h
    have hform' :
        G.projectAugmentString p₂' ++ R₂.2 ++ s₂.map symbol.terminal =
          G.projectAugmentString p₁' ++ R₁.2 ++ y.map symbol.terminal := by
      have h := congrArg G.projectAugmentString hform
      change
        G.projectAugmentString
            (p₂' ++ CF_grammar.augmentString R₂.2 ++
              s₂.map (symbol.terminal (N := Option G.nt))) =
          G.projectAugmentString
            (p₁' ++ CF_grammar.augmentString R₁.2 ++
              y.map (symbol.terminal (N := Option G.nt))) at h
      rw [projectAugmentString_post G R₂.2 p₂' s₂,
        projectAugmentString_post G R₁.2 p₁' y] at h
      exact h
    have hsame := hcore R₁ R₂ hR₁ hR₂
      (G.projectAugmentString p₁') (G.projectAugmentString p₂')
      s₁ s₂ y hd₁' hd₂' hform' hlook
    have hfree₁ := derivesRightmost_initial_or_avoids
      (fun rule hRule => augment_rule_rhs_avoids G rule hRule) hd₁
    have hfree₂ := derivesRightmost_initial_or_avoids
      (fun rule hRule => augment_rule_rhs_avoids G rule hRule) hd₂
    have hp₁Free : symbol.nonterminal G.augment.initial ∉ p₁ := by
      rcases hfree₁ with hstill | hav
      · exact False.elim (mapped_prehandle_ne_initial G R₁ p₁ s₁ hstill)
      · exact prefix_avoids_of_prehandle_avoids hav
    have hp₂Free : symbol.nonterminal G.augment.initial ∉ p₂ := by
      rcases hfree₂ with hstill | hav
      · exact False.elim (mapped_prehandle_ne_initial G R₂ p₂ s₂ hstill)
      · exact prefix_avoids_of_prehandle_avoids hav
    have hp₁Free' : symbol.nonterminal G.augment.initial ∉ p₁' := by
      simpa [p₁'] using hp₁Free
    have hp₂Free' : symbol.nonterminal G.augment.initial ∉ p₂' := by
      simpa [p₂'] using hp₂Free
    have hp : p₁' = p₂' :=
      projectAugmentString_injective_of_avoids G hp₁Free' hp₂Free' hsame.1
    exact ⟨by simpa [p₁', p₂'] using hp, by rw [hsame.2]⟩

end

end DPDA_to_LR
