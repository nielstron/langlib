module

public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.Linear.Closure.Union
public import Langlib.Classes.RecursivelyEnumerable.Closure.Reverse
public import Langlib.Examples.AbcPositive
import Langlib.Utilities.Tactics

@[expose]
public section

/-!
# A linear language outside the deterministic context-free class

This file supplies the linear half of the standard DCFL union counterexample.
The language
`lang_not_eq_any_pos + lang_not_any_eq_pos` consists of positive `a^i b^j c^k`
words for which either `i != j` or `j != k`.

The auxiliary grammar below generates
`x^(n+1) e^(d+1) y^(n+1) z^(k+1)`.  When `e` is `x` or `y`, this says that the
first two block lengths are unequal.  Reversing the grammar gives the analogous
comparison of the last two blocks.
-/

open Language List Relation Classical

noncomputable section

private inductive CmpState where
  | start
  | suffix
  | matched
  | extra
deriving DecidableEq

open CmpState

private def cmpStartRule (z : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], start, [], [symbol.nonterminal suffix, symbol.terminal z]⟩

private def cmpSuffixRule (z : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], suffix, [], [symbol.nonterminal suffix, symbol.terminal z]⟩

private def cmpToMatchedRule : grule (Fin 3) CmpState :=
  ⟨[], suffix, [], [symbol.nonterminal matched]⟩

private def cmpMatchedRule (x y : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], matched, [], [symbol.terminal x, symbol.nonterminal matched, symbol.terminal y]⟩

private def cmpToExtraRule (x y : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], matched, [], [symbol.terminal x, symbol.nonterminal extra, symbol.terminal y]⟩

private def cmpExtraRule (e : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], extra, [], [symbol.terminal e, symbol.nonterminal extra]⟩

private def cmpFinishRule (e : Fin 3) : grule (Fin 3) CmpState :=
  ⟨[], extra, [], [symbol.terminal e]⟩

/-- A linear grammar for `x^(n+1) e^(d+1) y^(n+1) z^(k+1)`. -/
@[reducible]
private def cmpGrammar (x y z e : Fin 3) : grammar (Fin 3) where
  nt := CmpState
  initial := start
  rules := [cmpStartRule z, cmpSuffixRule z, cmpToMatchedRule,
    cmpMatchedRule x y, cmpToExtraRule x y, cmpExtraRule e, cmpFinishRule e]

private lemma cmpGrammar_rule_cases (x y z e : Fin 3)
    {r : grule (Fin 3) CmpState} (hr : r ∈ (cmpGrammar x y z e).rules) :
    r = cmpStartRule z ∨ r = cmpSuffixRule z ∨ r = cmpToMatchedRule ∨
      r = cmpMatchedRule x y ∨ r = cmpToExtraRule x y ∨
      r = cmpExtraRule e ∨ r = cmpFinishRule e := by
  change r ∈ [cmpStartRule z, cmpSuffixRule z, cmpToMatchedRule,
    cmpMatchedRule x y, cmpToExtraRule x y, cmpExtraRule e, cmpFinishRule e] at hr
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inl hr
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr (Or.inl hr)
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr (Or.inr (Or.inl hr))
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
  rcases List.mem_cons.mp hr with hr | hr
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hr
  · exact (List.not_mem_nil hr).elim

private theorem cmpGrammar_is_linear (x y z e : Fin 3) :
    grammar_linear (cmpGrammar x y z e) := by
  unfold grammar_linear
  dsimp only [cmpGrammar]
  intro r hr
  rcases cmpGrammar_rule_cases x y z e hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cmpStartRule, cmpSuffixRule, cmpToMatchedRule, cmpMatchedRule,
      cmpToExtraRule, cmpExtraRule, cmpFinishRule] <;>
    refine ⟨trivial, trivial, ?_⟩
  · exact Or.inr ⟨[], suffix, [z], rfl⟩
  · exact Or.inr ⟨[], suffix, [z], rfl⟩
  · exact Or.inr ⟨[], matched, [], rfl⟩
  · exact Or.inr ⟨[x], matched, [y], rfl⟩
  · exact Or.inr ⟨[x], extra, [y], rfl⟩
  · exact Or.inr ⟨[e], extra, [], rfl⟩
  · exact Or.inl (by
      intro s hs
      exact ⟨e, List.mem_singleton.mp hs⟩)

private def cmpLanguage (x y z e : Fin 3) : Language (Fin 3) :=
  {w | ∃ n d k : ℕ,
    w = replicate (n + 1) x ++ replicate (d + 1) e ++
      replicate (n + 1) y ++ replicate (k + 1) z}

private lemma cmp_step_start (x y z e : Fin 3) :
    grammar_transforms (cmpGrammar x y z e)
      [symbol.nonterminal start]
      [symbol.nonterminal suffix, symbol.terminal z] := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpStartRule z, ?_, [], [], rfl, rfl⟩
  exact List.mem_cons_self

private lemma cmp_step_suffix (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal suffix] ++ right)
      (left ++ [symbol.nonterminal suffix, symbol.terminal z] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpSuffixRule z, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · change left ++ [symbol.nonterminal suffix] ++ right =
      left ++ [] ++ [symbol.nonterminal suffix] ++ [] ++ right
    simp
  · change left ++ [symbol.nonterminal suffix, symbol.terminal z] ++ right =
      left ++ [symbol.nonterminal suffix, symbol.terminal z] ++ right
    rfl

private lemma cmp_step_to_matched (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal suffix] ++ right)
      (left ++ [symbol.nonterminal matched] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpToMatchedRule, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · change left ++ [symbol.nonterminal suffix] ++ right =
      left ++ [] ++ [symbol.nonterminal suffix] ++ [] ++ right
    simp
  · change left ++ [symbol.nonterminal matched] ++ right =
      left ++ [symbol.nonterminal matched] ++ right
    rfl

private lemma cmp_step_matched (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal matched] ++ right)
      (left ++ [symbol.terminal x, symbol.nonterminal matched, symbol.terminal y] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpMatchedRule x y, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  · change left ++ [symbol.nonterminal matched] ++ right =
      left ++ [] ++ [symbol.nonterminal matched] ++ [] ++ right
    simp
  · change left ++ [symbol.terminal x, symbol.nonterminal matched, symbol.terminal y] ++ right =
      left ++ [symbol.terminal x, symbol.nonterminal matched, symbol.terminal y] ++ right
    rfl

private lemma cmp_step_to_extra (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal matched] ++ right)
      (left ++ [symbol.terminal x, symbol.nonterminal extra, symbol.terminal y] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpToExtraRule x y, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · change left ++ [symbol.nonterminal matched] ++ right =
      left ++ [] ++ [symbol.nonterminal matched] ++ [] ++ right
    simp
  · change left ++ [symbol.terminal x, symbol.nonterminal extra, symbol.terminal y] ++ right =
      left ++ [symbol.terminal x, symbol.nonterminal extra, symbol.terminal y] ++ right
    rfl

private lemma cmp_step_extra (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal extra] ++ right)
      (left ++ [symbol.terminal e, symbol.nonterminal extra] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpExtraRule e, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  · change left ++ [symbol.nonterminal extra] ++ right =
      left ++ [] ++ [symbol.nonterminal extra] ++ [] ++ right
    simp
  · change left ++ [symbol.terminal e, symbol.nonterminal extra] ++ right =
      left ++ [symbol.terminal e, symbol.nonterminal extra] ++ right
    rfl

private lemma cmp_step_finish (x y z e : Fin 3)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_transforms (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal extra] ++ right)
      (left ++ [symbol.terminal e] ++ right) := by
  unfold grammar_transforms
  dsimp only [cmpGrammar]
  refine ⟨cmpFinishRule e, ?_, left, right, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  · change left ++ [symbol.nonterminal extra] ++ right =
      left ++ [] ++ [symbol.nonterminal extra] ++ [] ++ right
    simp
  · change left ++ [symbol.terminal e] ++ right =
      left ++ [symbol.terminal e] ++ right
    rfl

private lemma cmp_derives_suffix (x y z e : Fin 3) (k : ℕ) :
    grammar_derives (cmpGrammar x y z e)
      [symbol.nonterminal start]
      ([symbol.nonterminal suffix] ++
        replicate (k + 1) (symbol.terminal z)) := by
  induction k with
  | zero => exact ReflTransGen.single (cmp_step_start x y z e)
  | succ k ih =>
      apply ih.tail
      change grammar_transforms (cmpGrammar x y z e)
        ([symbol.nonterminal suffix] ++ replicate (k + 1) (symbol.terminal z))
        ([symbol.nonterminal suffix, symbol.terminal z] ++
          replicate (k + 1) (symbol.terminal z))
      exact cmp_step_suffix x y z e [] (replicate (k + 1) (symbol.terminal z))

private lemma cmp_derives_matched (x y z e : Fin 3) (n : ℕ)
    (right : List (symbol (Fin 3) CmpState)) :
    grammar_derives (cmpGrammar x y z e)
      ([symbol.nonterminal matched] ++ right)
      (replicate n (symbol.terminal x) ++ [symbol.nonterminal matched] ++
        replicate n (symbol.terminal y) ++ right) := by
  induction n with
  | zero => simp; exact ReflTransGen.refl
  | succ n ih =>
      apply ih.tail
      have hx : replicate (n + 1) (symbol.terminal (N := CmpState) x) =
          replicate n (symbol.terminal (N := CmpState) x) ++
            [symbol.terminal (N := CmpState) x] := by
        exact List.replicate_succ'
      have hy : replicate (n + 1) (symbol.terminal (N := CmpState) y) =
          symbol.terminal (N := CmpState) y ::
            replicate n (symbol.terminal (N := CmpState) y) := by
        exact List.replicate_succ
      rw [hx, hy]
      simpa only [List.nil_append, List.singleton_append, List.cons_append,
        List.append_assoc] using
        cmp_step_matched x y z e
          (replicate n (symbol.terminal x))
          (replicate n (symbol.terminal y) ++ right)

private lemma cmp_derives_extra (x y z e : Fin 3) (d : ℕ)
    (left right : List (symbol (Fin 3) CmpState)) :
    grammar_derives (cmpGrammar x y z e)
      (left ++ [symbol.nonterminal extra] ++ right)
      (left ++ replicate d (symbol.terminal e) ++ [symbol.nonterminal extra] ++ right) := by
  induction d with
  | zero => simp; exact ReflTransGen.refl
  | succ d ih =>
      apply ih.tail
      have he : replicate (d + 1) (symbol.terminal (N := CmpState) e) =
          replicate d (symbol.terminal (N := CmpState) e) ++
            [symbol.terminal (N := CmpState) e] := by
        exact List.replicate_succ'
      rw [he]
      convert cmp_step_extra x y z e
        (left ++ replicate d (symbol.terminal e)) right using 1;
        simp only [List.nil_append, List.cons_append,
          List.append_assoc]

private lemma cmpLanguage_subset_grammar (x y z e : Fin 3) :
    Set.Subset (cmpLanguage x y z e) (grammar_language (cmpGrammar x y z e)) := by
  rintro w ⟨n, d, k, rfl⟩
  unfold grammar_language grammar_generates
  have hsuffix := cmp_derives_suffix x y z e k
  have htoMatched := ReflTransGen.single <|
    cmp_step_to_matched x y z e [] (replicate (k + 1) (symbol.terminal z))
  have hmatched := cmp_derives_matched x y z e n
    (replicate (k + 1) (symbol.terminal z))
  have htoExtra : grammar_derives (cmpGrammar x y z e)
      (replicate n (symbol.terminal x) ++ [symbol.nonterminal matched] ++
        replicate n (symbol.terminal y) ++ replicate (k + 1) (symbol.terminal z))
      ((replicate (n + 1) (symbol.terminal x) ++ [symbol.nonterminal extra]) ++
        (replicate (n + 1) (symbol.terminal y) ++
          replicate (k + 1) (symbol.terminal z))) := by
    have hx : replicate (n + 1) (symbol.terminal (N := CmpState) x) =
        replicate n (symbol.terminal (N := CmpState) x) ++
          [symbol.terminal (N := CmpState) x] := List.replicate_succ'
    have hy : replicate (n + 1) (symbol.terminal (N := CmpState) y) =
        symbol.terminal (N := CmpState) y ::
          replicate n (symbol.terminal (N := CmpState) y) := List.replicate_succ
    rw [hx, hy]
    exact ReflTransGen.single <| by
      simpa only [List.nil_append, List.singleton_append, List.cons_append,
        List.append_assoc] using
        cmp_step_to_extra x y z e
          (replicate n (symbol.terminal x))
          (replicate n (symbol.terminal y) ++ replicate (k + 1) (symbol.terminal z))
  have hextra := cmp_derives_extra x y z e d
    (replicate (n + 1) (symbol.terminal x))
    (replicate (n + 1) (symbol.terminal y) ++ replicate (k + 1) (symbol.terminal z))
  have hfinish := ReflTransGen.single <|
    cmp_step_finish x y z e
      (replicate (n + 1) (symbol.terminal x) ++ replicate d (symbol.terminal e))
      (replicate (n + 1) (symbol.terminal y) ++ replicate (k + 1) (symbol.terminal z))
  simpa [List.map_append, List.map_replicate, replicate_succ',
    List.append_assoc] using
    hsuffix.trans (htoMatched.trans (hmatched.trans (htoExtra.trans (hextra.trans hfinish))))

private def cmpSentential (x y z e : Fin 3)
    (s : List (symbol (Fin 3) CmpState)) : Prop :=
  s = [symbol.nonterminal start] ∨
  (∃ k : ℕ, s = [symbol.nonterminal suffix] ++
    replicate (k + 1) (symbol.terminal z)) ∨
  (∃ n k : ℕ, s = replicate n (symbol.terminal x) ++
    [symbol.nonterminal matched] ++ replicate n (symbol.terminal y) ++
    replicate (k + 1) (symbol.terminal z)) ∨
  (∃ n d k : ℕ, s = replicate (n + 1) (symbol.terminal x) ++
    replicate d (symbol.terminal e) ++ [symbol.nonterminal extra] ++
    replicate (n + 1) (symbol.terminal y) ++ replicate (k + 1) (symbol.terminal z)) ∨
  (∃ n d k : ℕ, s = List.map symbol.terminal
    (replicate (n + 1) x ++ replicate (d + 1) e ++
      replicate (n + 1) y ++ replicate (k + 1) z))

private lemma terminal_nonterminal_split_unique {T N : Type}
    {left right u v : List (symbol T N)} {A B : N}
    (hleft : ∀ s ∈ left, ∃ t, s = symbol.terminal t)
    (hright : ∀ s ∈ right, ∃ t, s = symbol.terminal t)
    (h : left ++ [symbol.nonterminal A] ++ right =
      u ++ [symbol.nonterminal B] ++ v) :
    left = u ∧ A = B ∧ right = v := by
  induction left generalizing u with
  | nil =>
      cases u with
      | nil =>
          simp only [List.nil_append, List.singleton_append] at h
          injection h with hAB hrv
          exact ⟨rfl, symbol.nonterminal.inj hAB, hrv⟩
      | cons q qs =>
          simp only [List.nil_append, List.cons_append] at h
          have htail := List.cons.inj h |>.2
          have hmem : symbol.nonterminal B ∈ right := by
            rw [htail]
            simp
          rcases hright _ hmem with ⟨t, ht⟩
          cases ht
  | cons p ps ih =>
      cases u with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have hp := hleft p (by simp)
          rcases hp with ⟨t, rfl⟩
          cases List.cons.inj h |>.1
      | cons q qs =>
          simp only [List.cons_append] at h
          have hpq := List.cons.inj h
          have hleft' : ∀ s ∈ ps, ∃ t, s = symbol.terminal t := by
            intro s hs
            exact hleft s (by simp [hs])
          rcases ih hleft' hpq.2 with ⟨hps, hAB, hrv⟩
          exact ⟨by rw [hpq.1, hps], hAB, hrv⟩

private lemma cmpSentential_step (x y z e : Fin 3)
    (s t : List (symbol (Fin 3) CmpState))
    (hs : cmpSentential x y z e s)
    (hst : grammar_transforms (cmpGrammar x y z e) s t) :
    cmpSentential x y z e t := by
  have terminal_replicate (q : Fin 3) (m : ℕ) :
      ∀ a ∈ replicate m (symbol.terminal (N := CmpState) q),
        ∃ q', a = symbol.terminal q' := by
    intro a ha
    exact ⟨q, List.eq_of_mem_replicate ha⟩
  have terminal_append {l₁ l₂ : List (symbol (Fin 3) CmpState)}
      (h₁ : ∀ a ∈ l₁, ∃ q, a = symbol.terminal q)
      (h₂ : ∀ a ∈ l₂, ∃ q, a = symbol.terminal q) :
      ∀ a ∈ l₁ ++ l₂, ∃ q, a = symbol.terminal q := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h₁ a ha
    · exact h₂ a ha
  unfold grammar_transforms at hst
  dsimp only [cmpGrammar] at hst
  rcases hst with ⟨r, hr, u, v, hbefore, rfl⟩
  rcases hs with hstart | ⟨k, hsuffix⟩ | ⟨n, k, hmatched⟩ |
      ⟨n, d, k, hextra⟩ | ⟨n, d, k, hfinal⟩
  · rw [hstart] at hbefore
    rcases cmpGrammar_rule_cases x y z e hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [cmpStartRule, cmpSuffixRule, cmpToMatchedRule, cmpMatchedRule,
      cmpToExtraRule, cmpExtraRule, cmpFinishRule,
      List.append_nil] at hbefore
    all_goals (
      obtain ⟨rfl, hstate, rfl⟩ := terminal_nonterminal_split_unique
        (left := []) (right := []) (u := u) (v := v)
        (by simp) (by simp) hbefore
      cases hstate <;>
        exact Or.inr (Or.inl ⟨0, by simp [cmpStartRule]⟩))
  · rw [hsuffix] at hbefore
    rcases cmpGrammar_rule_cases x y z e hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [cmpStartRule, cmpSuffixRule, cmpToMatchedRule, cmpMatchedRule,
      cmpToExtraRule, cmpExtraRule, cmpFinishRule,
      List.append_nil] at hbefore
    all_goals (
      obtain ⟨rfl, hstate, rfl⟩ := terminal_nonterminal_split_unique
        (left := [])
        (right := replicate (k + 1) (symbol.terminal z))
        (u := u) (v := v) (by simp) (terminal_replicate z (k + 1)) hbefore
      cases hstate <;>
        first
        | (refine Or.inr (Or.inl ⟨k + 1, ?_⟩)
           simp [cmpSuffixRule, replicate_succ]
           done)
        | (refine Or.inr (Or.inr (Or.inl ⟨0, k, ?_⟩))
           simp [cmpToMatchedRule]))
  · rw [hmatched] at hbefore
    rcases cmpGrammar_rule_cases x y z e hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [cmpStartRule, cmpSuffixRule, cmpToMatchedRule, cmpMatchedRule,
      cmpToExtraRule, cmpExtraRule, cmpFinishRule,
      List.append_nil] at hbefore
    all_goals (
      obtain ⟨rfl, hstate, rfl⟩ := terminal_nonterminal_split_unique
        (left := replicate n (symbol.terminal x))
        (right := replicate n (symbol.terminal y) ++
          replicate (k + 1) (symbol.terminal z))
        (u := u) (v := v) (terminal_replicate x n)
        (terminal_append (terminal_replicate y n)
          (terminal_replicate z (k + 1)))
        (by simpa only [List.append_assoc] using hbefore)
      cases hstate <;>
        first
        | (refine Or.inr (Or.inr (Or.inl ⟨n + 1, k, ?_⟩))
           have hx : replicate (n + 1) (symbol.terminal (N := CmpState) x) =
               replicate n (symbol.terminal x) ++ [symbol.terminal x] :=
             List.replicate_succ'
           have hy : replicate (n + 1) (symbol.terminal (N := CmpState) y) =
               symbol.terminal y :: replicate n (symbol.terminal y) :=
             List.replicate_succ
           rw [hx, hy]
           simp [cmpMatchedRule, List.append_assoc]
           done)
        | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, 0, k, ?_⟩)))
           have hx : replicate (n + 1) (symbol.terminal (N := CmpState) x) =
               replicate n (symbol.terminal x) ++ [symbol.terminal x] :=
             List.replicate_succ'
           have hy : replicate (n + 1) (symbol.terminal (N := CmpState) y) =
               symbol.terminal y :: replicate n (symbol.terminal y) :=
             List.replicate_succ
           rw [hx, hy]
           simp [cmpToExtraRule, List.append_assoc]))
  · rw [hextra] at hbefore
    rcases cmpGrammar_rule_cases x y z e hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [cmpStartRule, cmpSuffixRule, cmpToMatchedRule, cmpMatchedRule,
      cmpToExtraRule, cmpExtraRule, cmpFinishRule,
      List.append_nil] at hbefore
    all_goals (
      obtain ⟨rfl, hstate, rfl⟩ := terminal_nonterminal_split_unique
        (left := replicate (n + 1) (symbol.terminal x) ++
          replicate d (symbol.terminal e))
        (right := replicate (n + 1) (symbol.terminal y) ++
          replicate (k + 1) (symbol.terminal z))
        (u := u) (v := v)
        (terminal_append (terminal_replicate x (n + 1))
          (terminal_replicate e d))
        (terminal_append (terminal_replicate y (n + 1))
          (terminal_replicate z (k + 1)))
        (by simpa only [List.append_assoc] using hbefore)
      cases hstate <;>
        first
        | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, d + 1, k, ?_⟩)))
           have he : replicate (d + 1) (symbol.terminal (N := CmpState) e) =
               replicate d (symbol.terminal e) ++ [symbol.terminal e] :=
             List.replicate_succ'
           rw [he]
           simp [cmpExtraRule, List.append_assoc]
           done)
        | (refine Or.inr (Or.inr (Or.inr (Or.inr ⟨n, d, k, ?_⟩)))
           have he : replicate (d + 1) (symbol.terminal (N := CmpState) e) =
               replicate d (symbol.terminal e) ++ [symbol.terminal e] :=
             List.replicate_succ'
           simp only [List.map_append, List.map_replicate]
           rw [he]
           simp [cmpFinishRule, List.append_assoc]))
  · rw [hfinal] at hbefore
    have hmem : symbol.nonterminal r.input_N ∈
        List.map symbol.terminal
          (replicate (n + 1) x ++ replicate (d + 1) e ++
            replicate (n + 1) y ++ replicate (k + 1) z) := by
      rw [hbefore]
      simp
    simp at hmem

private lemma cmpSentential_of_derives (x y z e : Fin 3)
    (s : List (symbol (Fin 3) CmpState))
    (h : grammar_derives (cmpGrammar x y z e) [symbol.nonterminal start] s) :
    cmpSentential x y z e s := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih => exact cmpSentential_step x y z e _ _ ih hstep

private lemma grammar_subset_cmpLanguage (x y z e : Fin 3) :
    Set.Subset (grammar_language (cmpGrammar x y z e)) (cmpLanguage x y z e) := by
  intro w hw
  have hs := cmpSentential_of_derives x y z e (List.map symbol.terminal w) hw
  rcases hs with hstart | ⟨k, hsuffix⟩ | ⟨n, k, hmatched⟩ |
      ⟨n, d, k, hextra⟩ | ⟨n, d, k, hfinal⟩
  · no_nonterminal (symbol.nonterminal start) at hstart
  · no_nonterminal (symbol.nonterminal suffix) at hsuffix
  · no_nonterminal (symbol.nonterminal matched) at hmatched
  · no_nonterminal (symbol.nonterminal extra) at hextra
  · refine ⟨n, d, k, ?_⟩
    have hinj : Function.Injective
        (symbol.terminal (T := Fin 3) (N := CmpState)) := by
      intro p q hpq
      cases hpq
      rfl
    exact hinj.list_map hfinal

private theorem cmpGrammar_language (x y z e : Fin 3) :
    grammar_language (cmpGrammar x y z e) = cmpLanguage x y z e := by
  apply Set.Subset.antisymm
  · exact grammar_subset_cmpLanguage x y z e
  · exact cmpLanguage_subset_grammar x y z e

private theorem cmpLanguage_is_Linear (x y z e : Fin 3) :
    is_Linear (cmpLanguage x y z e) :=
  ⟨cmpGrammar x y z e, cmpGrammar_is_linear x y z e, cmpGrammar_language x y z e⟩

private theorem reversal_grammar_is_linear {T : Type} (g : grammar T)
    (hg : grammar_linear g) : grammar_linear (reversal_grammar g) := by
  intro r hr
  change r ∈ List.map reversal_grule g.rules at hr
  rcases List.mem_map.mp hr with ⟨r₀, hr₀, rfl⟩
  rcases hg r₀ hr₀ with ⟨hL, hR, hout⟩
  refine ⟨?_, ?_, ?_⟩
  · change r₀.input_R.reverse = []
    rw [hR]
    rfl
  · change r₀.input_L.reverse = []
    rw [hL]
    rfl
  rcases hout with hpure | ⟨u, B, v, hout⟩
  · left
    intro s hs
    change s ∈ r₀.output_string.reverse at hs
    have hs' : s ∈ r₀.output_string := List.mem_reverse.mp hs
    exact hpure s hs'
  · right
    refine ⟨v.reverse, B, u.reverse, ?_⟩
    simp only [reversal_grule, hout, List.reverse_append, List.reverse_singleton,
      List.map_reverse]
    simp only [List.append_assoc]
    rfl

private theorem is_Linear_reverse {T : Type} {L : Language T}
    (hL : is_Linear L) : is_Linear L.reverse := by
  rcases hL with ⟨g, hg, rfl⟩
  exact ⟨reversal_grammar g, reversal_grammar_is_linear g hg,
    grammar_language_reversal_grammar g⟩

private def abLt : Language (Fin 3) := cmpLanguage a_ b_ c_ b_
private def abGt : Language (Fin 3) := cmpLanguage a_ b_ c_ a_
private def bcLt : Language (Fin 3) := (cmpLanguage c_ b_ a_ c_).reverse
private def bcGt : Language (Fin 3) := (cmpLanguage c_ b_ a_ b_).reverse

private theorem abLt_is_Linear : is_Linear abLt :=
  cmpLanguage_is_Linear a_ b_ c_ b_

private theorem abGt_is_Linear : is_Linear abGt :=
  cmpLanguage_is_Linear a_ b_ c_ a_

private theorem bcLt_is_Linear : is_Linear bcLt :=
  is_Linear_reverse (cmpLanguage_is_Linear c_ b_ a_ c_)

private theorem bcGt_is_Linear : is_Linear bcGt :=
  is_Linear_reverse (cmpLanguage_is_Linear c_ b_ a_ b_)

private theorem ab_union : abLt + abGt = lang_not_eq_any_pos := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hw | hw
    · rcases hw with ⟨n, d, k, rfl⟩
      constructor
      · intro heq
        rcases heq.1 with ⟨q, r, hq⟩
        have ha := congrArg (List.count a_) hq
        have hb := congrArg (List.count b_) hq
        simp +decide [a_, b_, c_, List.count_append, List.count_replicate] at ha hb
        omega
      · refine ⟨n, d + n + 1, k, ?_⟩
        simp only [← List.replicate_add, List.append_assoc]
        rw [show d + 1 + (n + 1) = d + n + 1 + 1 by omega]
    · rcases hw with ⟨n, d, k, rfl⟩
      constructor
      · intro heq
        rcases heq.1 with ⟨q, r, hq⟩
        have ha := congrArg (List.count a_) hq
        have hb := congrArg (List.count b_) hq
        simp +decide [a_, b_, c_, List.count_append, List.count_replicate] at ha hb
        omega
      · refine ⟨d + n + 1, n, k, ?_⟩
        simp only [← List.replicate_add, List.append_assoc]
        rw [show n + 1 + (d + 1) = d + n + 1 + 1 by omega]
  · intro hw
    rcases hw.2 with ⟨n, m, k, rfl⟩
    have hne : n ≠ m := by
      intro hnm
      apply hw.1
      constructor
      · refine ⟨n + 1, k + 1, ?_⟩
        simp [hnm]
      · exact ⟨n, m, k, rfl⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rcases Nat.exists_eq_add_of_lt hlt with ⟨d, rfl⟩
      rw [Language.mem_add]
      left
      refine ⟨n, d, k, ?_⟩
      simp only [← List.replicate_add, List.append_assoc]
      rw [show n + d + 1 + 1 = d + 1 + (n + 1) by omega]
    · rcases Nat.exists_eq_add_of_lt hgt with ⟨d, rfl⟩
      rw [Language.mem_add]
      right
      refine ⟨m, d, k, ?_⟩
      simp only [← List.replicate_add, List.append_assoc]
      rw [show m + d + 1 + 1 = m + 1 + (d + 1) by omega]

private theorem bc_union : bcLt + bcGt = lang_not_any_eq_pos := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hw | hw
    · rcases Language.mem_reverse.mp hw with ⟨n, d, k, hrev⟩
      have hword := congrArg List.reverse hrev
      simp only [List.reverse_append, List.reverse_replicate,
        List.reverse_reverse] at hword
      rw [hword]
      constructor
      · intro heq
        rcases heq.1 with ⟨q, r, hq⟩
        have hb := congrArg (List.count b_) hq
        have hc := congrArg (List.count c_) hq
        simp +decide [a_, b_, c_, List.count_append, List.count_replicate] at hb hc
        omega
      · refine ⟨k, n, d + n + 1, ?_⟩
        simp only [← List.replicate_add, List.append_assoc]
        rw [show d + 1 + (n + 1) = d + n + 1 + 1 by omega]
    · rcases Language.mem_reverse.mp hw with ⟨n, d, k, hrev⟩
      have hword := congrArg List.reverse hrev
      simp only [List.reverse_append, List.reverse_replicate,
        List.reverse_reverse] at hword
      rw [hword]
      constructor
      · intro heq
        rcases heq.1 with ⟨q, r, hq⟩
        have hb := congrArg (List.count b_) hq
        have hc := congrArg (List.count c_) hq
        simp +decide [a_, b_, c_, List.count_append, List.count_replicate] at hb hc
        omega
      · refine ⟨k, d + n + 1, n, ?_⟩
        have hmerge : replicate (n + 1) b_ ++ replicate (d + 1) b_ =
            replicate (d + n + 1 + 1) b_ := by
          rw [← List.replicate_add]
          congr 1
          omega
        rw [← List.append_assoc (replicate (n + 1) b_)
          (replicate (d + 1) b_) (replicate (n + 1) c_), hmerge]
        simp only [List.append_assoc]
  · intro hw
    rcases hw.2 with ⟨n, m, k, rfl⟩
    have hne : m ≠ k := by
      intro hmk
      apply hw.1
      constructor
      · refine ⟨n + 1, m + 1, ?_⟩
        simp [hmk]
      · exact ⟨n, m, k, rfl⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rcases Nat.exists_eq_add_of_lt hlt with ⟨d, rfl⟩
      rw [Language.mem_add]
      left
      apply Language.mem_reverse.mpr
      refine ⟨m, d, n, ?_⟩
      simp only [List.reverse_append, List.reverse_replicate,
        ← List.replicate_add, List.append_assoc]
      rw [show m + d + 1 + 1 = m + 1 + (d + 1) by omega]
    · rcases Nat.exists_eq_add_of_lt hgt with ⟨d, rfl⟩
      rw [Language.mem_add]
      right
      apply Language.mem_reverse.mpr
      refine ⟨k, d, n, ?_⟩
      simp only [List.reverse_append, List.reverse_replicate,
        ← List.replicate_add, List.append_assoc]
      rw [show k + d + 1 + 1 = d + 1 + (k + 1) by omega]

/-- The positive `a^i b^j c^k` words satisfying `i ≠ j` or `j ≠ k`
form a linear language. -/
public theorem notEqUnion_is_Linear :
    is_Linear (lang_not_eq_any_pos + lang_not_any_eq_pos) := by
  rw [← ab_union, ← bc_union]
  exact Linear_closedUnderUnion _ _
    (Linear_closedUnderUnion _ _ abLt_is_Linear abGt_is_Linear)
    (Linear_closedUnderUnion _ _ bcLt_is_Linear bcGt_is_Linear)

end

end
