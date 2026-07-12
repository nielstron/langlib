module

public import Langlib.Classes.Indexed.Closure.Concatenation
public import Langlib.Classes.Indexed.Closure.Homomorphism
public import Langlib.Classes.Indexed.Closure.Star
public import Langlib.Classes.Indexed.Closure.Substitution
public import Langlib.Classes.Indexed.Examples.SingletonWord
public import Langlib.Classes.Regular.Inclusion.ContextFree
public import Langlib.Grammars.Indexed.NormalForm.Derivation
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Inclusion.Indexed
import Langlib.Classes.ContextFree.Closure.InverseHomomorphism
import Langlib.Automata.FiniteState.Equivalence.Regular
import Mathlib.Tactic

@[expose]
public section

/-!
# Indexed Languages Are Closed Under Inverse Homomorphism

The proof factors inverse homomorphism through a block coding. Its only substantial auxiliary
ingredient is the standard indexed-grammar product with a DFA, used to intersect an indexed
language with the regular block-code language.
-/

open List
open Classical

noncomputable section

variable {T Q : Type} [Fintype Q]

private def ProductNT (g : IndexedGrammar T) (Q : Type) := Option (Q × g.nt × Q)

private def threadIRhs (D : DFA T Q) (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (p : Q) :
    List (List (IRhsSymbol T (ProductNT g Q) g.flag) × Q) :=
  match rhs with
  | [] => [([], p)]
  | .terminal a :: rest =>
      (threadIRhs D g rest (D.step p a)).map fun ⟨out, q⟩ =>
        (.terminal a :: out, q)
  | .nonterminal B push :: rest =>
      Finset.univ.toList.flatMap fun mid =>
        (threadIRhs D g rest mid).map fun ⟨out, q⟩ =>
          (.nonterminal (some (p, B, mid)) push :: out, q)

private def productStartRules (g : IndexedGrammar T) (D : DFA T Q) :
    List (IRule T (ProductNT g Q) g.flag) :=
  (Finset.univ.filter (· ∈ D.accept)).toList.map fun q =>
    { lhs := none
      consume := none
      rhs := [.nonterminal (some (D.start, g.initial, q)) none] }

private def productBodyRules (g : IndexedGrammar T) (D : DFA T Q) :
    List (IRule T (ProductNT g Q) g.flag) :=
  g.rules.flatMap fun r =>
    Finset.univ.toList.flatMap fun p =>
      (threadIRhs D g r.rhs p).map fun ⟨out, q⟩ =>
        { lhs := some (p, r.lhs, q), consume := r.consume, rhs := out }

private def indexedDFAProduct (g : IndexedGrammar T) (D : DFA T Q) : IndexedGrammar T where
  nt := ProductNT g Q
  flag := g.flag
  initial := none
  rules := productStartRules g D ++ productBodyRules g D

private inductive ThreadsForm (g : IndexedGrammar T) (D : DFA T Q) :
    List g.ISym → Q → List (indexedDFAProduct g D).ISym → Q → Prop
  | nil (p) : ThreadsForm g D [] p [] p
  | terminal {rest out p q} (a : T) :
      ThreadsForm g D rest (D.step p a) out q →
      ThreadsForm g D (.terminal a :: rest) p (.terminal a :: out) q
  | indexed {rest out p mid q} (A : g.nt) (σ : List g.flag) :
      ThreadsForm g D rest mid out q →
      ThreadsForm g D (.indexed A σ :: rest) p
        (.indexed (some (p, A, mid)) σ :: out) q

private inductive ThreadsRhs (g : IndexedGrammar T) (D : DFA T Q) :
    List (IRhsSymbol T g.nt g.flag) → Q →
      List (IRhsSymbol T (ProductNT g Q) g.flag) → Q → Prop
  | nil (p) : ThreadsRhs g D [] p [] p
  | terminal {rest out p q} (a : T) :
      ThreadsRhs g D rest (D.step p a) out q →
      ThreadsRhs g D (.terminal a :: rest) p (.terminal a :: out) q
  | nonterminal {rest out p mid q} (A : g.nt) (push : Option g.flag) :
      ThreadsRhs g D rest mid out q →
      ThreadsRhs g D (.nonterminal A push :: rest) p
        (.nonterminal (some (p, A, mid)) push :: out) q

private lemma ThreadsRhs.mem_threadIRhs {g : IndexedGrammar T} {D : DFA T Q}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {p q : Q}
    {out : List (IRhsSymbol T (ProductNT g Q) g.flag)}
    (h : ThreadsRhs g D rhs p out q) : (out, q) ∈ threadIRhs D g rhs p := by
  induction h with
  | nil => simp [threadIRhs]
  | terminal a _ ih => simp [threadIRhs, ih]
  | nonterminal A push _ ih =>
      simp only [threadIRhs, List.mem_flatMap, Finset.mem_toList,
        Finset.mem_univ, true_and, List.mem_map]
      exact ⟨_, (_, _), ih, rfl⟩

private lemma threadIRhs_mem_iff (D : DFA T Q) (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (p q : Q)
    (out : List (IRhsSymbol T (ProductNT g Q) g.flag)) :
    (out, q) ∈ threadIRhs D g rhs p ↔ ThreadsRhs g D rhs p out q := by
  induction rhs generalizing p out q with
  | nil =>
      simp only [threadIRhs, List.mem_singleton]
      constructor
      · intro h
        cases h
        exact ThreadsRhs.nil p
      · intro h
        cases h
        rfl
  | cons s rhs ih =>
      cases s with
      | terminal a =>
          simp only [threadIRhs, List.mem_map]
          constructor
          · rintro ⟨⟨out', q'⟩, hm, hEq⟩
            cases hEq
            exact ThreadsRhs.terminal a ((ih _ _ _).mp hm)
          · intro h
            simpa only [threadIRhs, List.mem_map] using
              (ThreadsRhs.mem_threadIRhs (T := T) (Q := Q) h)
      | nonterminal A push =>
          simp only [threadIRhs, List.mem_flatMap, Finset.mem_toList,
            Finset.mem_univ, true_and, List.mem_map]
          constructor
          · rintro ⟨mid, ⟨out', q'⟩, hm, hEq⟩
            cases hEq
            exact ThreadsRhs.nonterminal A push ((ih _ _ _).mp hm)
          · intro h
            simpa only [threadIRhs, List.mem_flatMap, Finset.mem_toList,
              Finset.mem_univ, true_and, List.mem_map] using
              (ThreadsRhs.mem_threadIRhs (T := T) (Q := Q) h)

private lemma ThreadsRhs.expand {g : IndexedGrammar T} {D : DFA T Q}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {p q : Q}
    {out : List (IRhsSymbol T (ProductNT g Q) g.flag)}
    (h : ThreadsRhs g D rhs p out q) (σ : List g.flag) :
    ThreadsForm g D (g.expandRhs rhs σ) p
      ((indexedDFAProduct g D).expandRhs out σ) q := by
  induction h with
  | nil => exact ThreadsForm.nil _
  | terminal a _ ih => exact ThreadsForm.terminal a ih
  | nonterminal A push _ ih =>
      cases push with
      | none =>
          simp only [IndexedGrammar.expandRhs]
          apply ThreadsForm.indexed
          exact ih
      | some f =>
          simp only [IndexedGrammar.expandRhs]
          apply ThreadsForm.indexed
          exact ih

private lemma product_body_rule_mem (g : IndexedGrammar T) (D : DFA T Q)
    (p q : Q) (A : g.nt) (consume : Option g.flag)
    (out : List (IRhsSymbol T (ProductNT g Q) g.flag))
    (h : ({ lhs := some (p, A, q), consume := consume, rhs := out } :
      IRule T (ProductNT g Q) g.flag) ∈ (indexedDFAProduct g D).rules) :
    ∃ r ∈ g.rules, r.lhs = A ∧ r.consume = consume ∧
      (out, q) ∈ threadIRhs D g r.rhs p := by
  unfold indexedDFAProduct productStartRules productBodyRules at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | h
  · rcases h with ⟨x, _, hEq⟩
    cases hEq
  · rcases h with ⟨r, hr, p', outq, houtq, hEq⟩
    cases hEq
    exact ⟨r, hr, rfl, rfl, houtq⟩

private lemma product_start_rule_mem (g : IndexedGrammar T) (D : DFA T Q)
    (q : Q) (hq : q ∈ D.accept) :
    ({ lhs := none, consume := none,
       rhs := [.nonterminal (some (D.start, g.initial, q)) none] } :
      IRule T (ProductNT g Q) g.flag) ∈ (indexedDFAProduct g D).rules := by
  unfold indexedDFAProduct productStartRules
  apply List.mem_append_left
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨q, hq, rfl⟩

private lemma forward_form (g : IndexedGrammar T) (D : DFA T Q) (bound : ℕ)
    {xs : List g.ISym} {p q : Q}
    {ys : List (indexedDFAProduct g D).ISym}
    (hform : ThreadsForm g D xs p ys q) {n : ℕ} {w : List T}
    (hn : n < bound)
    (hder : (indexedDFAProduct g D).DerivesIn n ys
      (w.map fun a => IndexedGrammar.ISym.terminal a))
    (ih : ∀ k < bound, ∀ (p' : Q) (A' : g.nt) (q' : Q)
        (σ : List g.flag) (w' : List T),
      (indexedDFAProduct g D).DerivesIn k
          [.indexed (some (p', A', q')) σ]
          (w'.map fun a => IndexedGrammar.ISym.terminal a) →
      g.Derives [.indexed A' σ]
          (w'.map fun a => IndexedGrammar.ISym.terminal a) ∧
        D.evalFrom p' w' = q') :
    g.Derives xs (w.map fun a => IndexedGrammar.ISym.terminal a) ∧
      D.evalFrom p w = q := by
  induction hform generalizing n w with
  | nil p =>
      obtain ⟨hn0, hw⟩ := IndexedGrammar.derivesIn_nil_left_eq hder
      subst n
      simp at hw
      subst w
      exact ⟨g.deri_self [], rfl⟩
  | terminal a _ hrec =>
      rename_i xsRest ysRest p₀ q₀
      have hs := IndexedGrammar.derivesIn_append_to_terminals_split
        (g := indexedDFAProduct g D)
        (u := [.terminal a]) (v := xsRest) hder
      rcases hs with ⟨m, k, u, v, hmk, hw, hu, hv⟩
      have huword := IndexedGrammar.derivesIn_terminal_singleton_eq hu
      have hm0 := IndexedGrammar.derivesIn_terminal_singleton_steps_eq_zero hu
      subst u
      subst m
      simp at hmk
      subst n
      rcases hrec (n := k) (w := v) hn hv with ⟨hg, heval⟩
      subst w
      refine ⟨?_, ?_⟩
      · simpa [List.map_append] using
          (IndexedGrammar.deri_with_prefix
            ([.terminal a] : List g.ISym) hg)
      · simpa [DFA.evalFrom, DFA.evalFrom_of_append, heval]
  | indexed A σ _ hrec =>
      rename_i xsRest ysRest p₀ mid₀ q₀
      have hs := IndexedGrammar.derivesIn_append_to_terminals_split
        (g := indexedDFAProduct g D)
        (u := [.indexed (some (ysRest, A, p₀)) σ]) (v := xsRest) hder
      rcases hs with ⟨m, k, u, v, hmk, hw, hu, hv⟩
      have hm : m < bound := by omega
      have hk : k < bound := by omega
      rcases ih m hm ysRest A p₀ σ u hu with ⟨hleft, hevalLeft⟩
      rcases hrec (n := k) (w := v) hk hv with ⟨hright, hevalRight⟩
      subst w
      refine ⟨?_, ?_⟩
      · simpa [List.map_append] using
          (IndexedGrammar.deri_with_suffix _ hleft).trans
            (IndexedGrammar.deri_with_prefix
              (u.map fun a => (IndexedGrammar.ISym.terminal a : g.ISym)) hright)
      · simpa [DFA.evalFrom_of_append, hevalLeft, hevalRight]

private lemma singleton_eq_append_singleton {X : Type} {a b : X}
    {u v : List X} (h : [a] = u ++ [b] ++ v) :
    u = [] ∧ v = [] ∧ a = b := by
  have hlen := congrArg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
  have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
  subst u
  subst v
  simpa using h

private lemma forward_key (g : IndexedGrammar T) (D : DFA T Q)
    (n : ℕ) (p : Q) (A : g.nt) (q : Q) (σ : List g.flag) (w : List T)
    (hder : (indexedDFAProduct g D).DerivesIn n
      [.indexed (some (p, A, q)) σ]
      (w.map fun a => IndexedGrammar.ISym.terminal a)) :
    g.Derives [.indexed A σ]
        (w.map fun a => IndexedGrammar.ISym.terminal a) ∧
      D.evalFrom p w = q := by
  induction n using Nat.strong_induction_on generalizing p A q σ w with
  | h n ih =>
      cases n with
      | zero =>
          cases w <;> simp at hder
      | succ n =>
          have hsplit : (indexedDFAProduct g D).DerivesIn (1 + n)
              [.indexed (some (p, A, q)) σ]
              (w.map fun a => IndexedGrammar.ISym.terminal a) := by
            convert hder using 1 <;> omega
          rcases IndexedGrammar.derivesIn_split (m := 1) (n := n) hsplit with
            ⟨midForm, hfirst, hrest⟩
          rcases hfirst with ⟨before, hzero, hstep⟩
          simp at hzero
          subst before
          rcases hstep with ⟨r, u, v, τ, hr, hsource, htarget⟩
          cases hc : r.consume with
          | none =>
              have hs : [.indexed (some (p, A, q)) σ] =
                  u ++ [.indexed r.lhs τ] ++ v := by
                simpa [hc] using hsource
              rcases singleton_eq_append_singleton hs with ⟨rfl, rfl, hsym⟩
              simp only [List.nil_append, List.append_nil] at htarget
              subst midForm
              injection hsym with hlhs hstack
              subst τ
              have hrule : (⟨some (p, A, q), (none : Option g.flag), r.rhs⟩ :
                  IRule T (ProductNT g Q) g.flag) ∈
                  (indexedDFAProduct g D).rules := by
                have req : r =
                    (⟨some (p, A, q), (none : Option g.flag), r.rhs⟩ :
                      IRule T (ProductNT g Q) g.flag) := by
                  cases r
                  simp_all
                exact req ▸ hr
              rcases product_body_rule_mem g D p q A none r.rhs hrule with
                ⟨r₀, hr₀, hlhs₀, hconsume₀, hthread⟩
              have htf := (threadIRhs_mem_iff D g r₀.rhs p q r.rhs).mp hthread
              have hf := forward_form g D (n + 1) (htf.expand σ)
                (Nat.lt_succ_self n) hrest
                (fun k hk p' A' q' σ' w' hd =>
                  ih k (by omega) p' A' q' σ' w' hd)
              refine ⟨?_, hf.2⟩
              apply IndexedGrammar.deri_of_tran_deri
              · refine ⟨r₀, [], [], σ, hr₀, ?_, rfl⟩
                rw [hconsume₀]
                simp [hlhs₀]
              · simpa using hf.1
          | some f =>
              have hs : [.indexed (some (p, A, q)) σ] =
                  u ++ [.indexed r.lhs (f :: τ)] ++ v := by
                simpa [hc] using hsource
              rcases singleton_eq_append_singleton hs with ⟨rfl, rfl, hsym⟩
              simp only [List.nil_append, List.append_nil] at htarget
              subst midForm
              injection hsym with hlhs hstack
              have hrule : (⟨some (p, A, q), (some f : Option g.flag), r.rhs⟩ :
                  IRule T (ProductNT g Q) g.flag) ∈
                  (indexedDFAProduct g D).rules := by
                have req : r =
                    (⟨some (p, A, q), (some f : Option g.flag), r.rhs⟩ :
                      IRule T (ProductNT g Q) g.flag) := by
                  cases r
                  simp_all
                exact req ▸ hr
              rcases product_body_rule_mem g D p q A (some f) r.rhs hrule with
                ⟨r₀, hr₀, hlhs₀, hconsume₀, hthread⟩
              have htf := (threadIRhs_mem_iff D g r₀.rhs p q r.rhs).mp hthread
              have hf := forward_form g D (n + 1) (htf.expand τ)
                (Nat.lt_succ_self n) hrest
                (fun k hk p' A' q' σ' w' hd =>
                  ih k (by omega) p' A' q' σ' w' hd)
              refine ⟨?_, hf.2⟩
              apply IndexedGrammar.deri_of_tran_deri
              · refine ⟨r₀, [], [], τ, hr₀, ?_, rfl⟩
                rw [hconsume₀]
                simp [hlhs₀, hstack]
              · simpa using hf.1

private lemma product_body_rule_intro (g : IndexedGrammar T) (D : DFA T Q)
    (r : IRule T g.nt g.flag) (hr : r ∈ g.rules) (p q : Q)
    (out : List (IRhsSymbol T (ProductNT g Q) g.flag))
    (hout : (out, q) ∈ threadIRhs D g r.rhs p) :
    ({ lhs := some (p, r.lhs, q), consume := r.consume, rhs := out } :
      IRule T (ProductNT g Q) g.flag) ∈ (indexedDFAProduct g D).rules := by
  unfold indexedDFAProduct productBodyRules
  apply List.mem_append_right
  simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
    true_and, List.mem_map]
  exact ⟨r, hr, p, (out, q), hout, rfl⟩

private lemma backward_rhs (g : IndexedGrammar T) (D : DFA T Q) (bound : ℕ)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag)
    (p q : Q) {n : ℕ} {w : List T}
    (hn : n < bound)
    (hder : g.DerivesIn n (g.expandRhs rhs σ)
      (w.map fun a => IndexedGrammar.ISym.terminal a))
    (heval : D.evalFrom p w = q)
    (ih : ∀ k < bound, ∀ (A' : g.nt) (σ' : List g.flag)
        (w' : List T) (p' q' : Q),
      g.DerivesIn k [.indexed A' σ']
          (w'.map fun a => IndexedGrammar.ISym.terminal a) →
      D.evalFrom p' w' = q' →
      (indexedDFAProduct g D).Derives
          [.indexed (some (p', A', q')) σ']
          (w'.map fun a => IndexedGrammar.ISym.terminal a)) :
    ∃ out : List (IRhsSymbol T (ProductNT g Q) g.flag),
      ThreadsRhs g D rhs p out q ∧
        (indexedDFAProduct g D).Derives
          ((indexedDFAProduct g D).expandRhs out σ)
          (w.map fun a => IndexedGrammar.ISym.terminal a) := by
  induction rhs generalizing p q n w with
  | nil =>
      obtain ⟨hn0, hw⟩ := IndexedGrammar.derivesIn_nil_left_eq hder
      subst n
      simp at hw
      subst w
      simp at heval
      subst q
      exact ⟨[], ThreadsRhs.nil p, (indexedDFAProduct g D).deri_self []⟩
  | cons s rhs hrec =>
      cases s with
      | terminal a =>
          have hs := IndexedGrammar.derivesIn_append_to_terminals_split
            (g := g) (u := [.terminal a]) (v := g.expandRhs rhs σ) hder
          rcases hs with ⟨m, k, u, v, hmk, hw, hu, hv⟩
          have huword := IndexedGrammar.derivesIn_terminal_singleton_eq hu
          have hm0 := IndexedGrammar.derivesIn_terminal_singleton_steps_eq_zero hu
          subst u
          subst m
          simp at hmk
          subst n
          subst w
          have htailEval : D.evalFrom (D.step p a) v = q := by
            simpa [DFA.evalFrom, DFA.evalFrom_of_append] using heval
          rcases hrec (D.step p a) q (n := k) (w := v) hn hv htailEval with
            ⟨out, hthread, houtDer⟩
          refine ⟨.terminal a :: out, ThreadsRhs.terminal a hthread, ?_⟩
          simpa [IndexedGrammar.expandRhs, List.map_append] using
            IndexedGrammar.deri_with_prefix
              ([.terminal a] : List (indexedDFAProduct g D).ISym) houtDer
      | nonterminal A push =>
          let stack := match push with | none => σ | some f => f :: σ
          have hexpand : g.expandRhs (.nonterminal A push :: rhs) σ =
              .indexed A stack :: g.expandRhs rhs σ := by
            cases push <;> rfl
          have hs := IndexedGrammar.derivesIn_append_to_terminals_split
            (g := g) (u := [.indexed A stack]) (v := g.expandRhs rhs σ)
            (by simpa [hexpand] using hder)
          rcases hs with ⟨m, k, u, v, hmk, hw, hu, hv⟩
          have hm : m < bound := by omega
          have hk : k < bound := by omega
          let mid := D.evalFrom p u
          have hleft := ih m hm A stack u p mid hu rfl
          have htailEval : D.evalFrom mid v = q := by
            rw [hw, DFA.evalFrom_of_append] at heval
            simpa [mid] using heval
          rcases hrec mid q (n := k) (w := v) hk hv htailEval with
            ⟨out, hthread, houtDer⟩
          refine ⟨.nonterminal (some (p, A, mid)) push :: out,
            ThreadsRhs.nonterminal A push hthread, ?_⟩
          have hcombined :=
            (IndexedGrammar.deri_with_suffix _ hleft).trans
              (IndexedGrammar.deri_with_prefix
                (u.map fun a =>
                  (IndexedGrammar.ISym.terminal a : (indexedDFAProduct g D).ISym))
                houtDer)
          rw [hw]
          cases push <;>
            simpa [IndexedGrammar.expandRhs, stack, List.map_append] using hcombined

private lemma backward_key (g : IndexedGrammar T) (D : DFA T Q)
    (n : ℕ) (A : g.nt) (σ : List g.flag) (w : List T) (p q : Q)
    (hder : g.DerivesIn n [.indexed A σ]
      (w.map fun a => IndexedGrammar.ISym.terminal a))
    (heval : D.evalFrom p w = q) :
    (indexedDFAProduct g D).Derives
      [.indexed (some (p, A, q)) σ]
      (w.map fun a => IndexedGrammar.ISym.terminal a) := by
  induction n using Nat.strong_induction_on generalizing A σ w p q with
  | h n ih =>
      cases n with
      | zero =>
          cases w <;> simp at hder
      | succ n =>
          have hsplit : g.DerivesIn (1 + n) [.indexed A σ]
              (w.map fun a => IndexedGrammar.ISym.terminal a) := by
            convert hder using 1 <;> omega
          rcases IndexedGrammar.derivesIn_split (m := 1) (n := n) hsplit with
            ⟨midForm, hfirst, hrest⟩
          rcases hfirst with ⟨before, hzero, hstep⟩
          simp at hzero
          subst before
          rcases hstep with ⟨r, u, v, τ, hr, hsource, htarget⟩
          cases hc : r.consume with
          | none =>
              have hs : [.indexed A σ] = u ++ [.indexed r.lhs τ] ++ v := by
                simpa [hc] using hsource
              rcases singleton_eq_append_singleton hs with ⟨rfl, rfl, hsym⟩
              simp only [List.nil_append, List.append_nil] at htarget
              subst midForm
              injection hsym with hlhs hstack
              subst τ
              rcases backward_rhs g D (n + 1) r.rhs σ p q
                  (Nat.lt_succ_self n) hrest heval
                  (fun k hk A' σ' w' p' q' hd he =>
                    ih k (by omega) A' σ' w' p' q' hd he) with
                ⟨out, hthread, houtDer⟩
              have hprodRule := product_body_rule_intro g D r hr p q out
                hthread.mem_threadIRhs
              have hprodRule' :
                  ({ lhs := some (p, r.lhs, q), consume := none, rhs := out } :
                    IRule T (ProductNT g Q) g.flag) ∈
                    (indexedDFAProduct g D).rules := by
                simpa [hc] using hprodRule
              apply IndexedGrammar.deri_of_tran_deri
              · refine ⟨{ lhs := some (p, r.lhs, q), consume := none, rhs := out },
                  [], [], σ, hprodRule', ?_, rfl⟩
                simp [hlhs]
              · simpa using houtDer
          | some f =>
              have hs : [.indexed A σ] = u ++ [.indexed r.lhs (f :: τ)] ++ v := by
                simpa [hc] using hsource
              rcases singleton_eq_append_singleton hs with ⟨rfl, rfl, hsym⟩
              simp only [List.nil_append, List.append_nil] at htarget
              subst midForm
              injection hsym with hlhs hstack
              rcases backward_rhs g D (n + 1) r.rhs τ p q
                  (Nat.lt_succ_self n) hrest heval
                  (fun k hk A' σ' w' p' q' hd he =>
                    ih k (by omega) A' σ' w' p' q' hd he) with
                ⟨out, hthread, houtDer⟩
              have hprodRule := product_body_rule_intro g D r hr p q out
                hthread.mem_threadIRhs
              have hprodRule' :
                  ({ lhs := some (p, r.lhs, q), consume := some f, rhs := out } :
                    IRule T (ProductNT g Q) g.flag) ∈
                    (indexedDFAProduct g D).rules := by
                simpa [hc] using hprodRule
              apply IndexedGrammar.deri_of_tran_deri
              · refine ⟨{ lhs := some (p, r.lhs, q), consume := some f, rhs := out },
                  [], [], τ, hprodRule', ?_, rfl⟩
                simp [hlhs, hstack]
              · simpa using houtDer

private lemma product_rule_with_none_lhs (g : IndexedGrammar T) (D : DFA T Q)
    (r : IRule T (ProductNT g Q) g.flag)
    (hr : r ∈ (indexedDFAProduct g D).rules) (hlhs : r.lhs = none) :
    ∃ q ∈ D.accept, r.consume = none ∧
      r.rhs = [.nonterminal (some (D.start, g.initial, q)) none] := by
  unfold indexedDFAProduct productStartRules productBodyRules at hr
  simp only [List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and, List.mem_flatMap] at hr
  rcases hr with hstart | hbody
  · rcases hstart with ⟨q, hq, hEq⟩
    cases hEq
    exact ⟨q, hq, rfl, rfl⟩
  · rcases hbody with ⟨r₀, hr₀, p, outq, houtq, hEq⟩
    cases hEq
    simp at hlhs

private lemma product_initial_step (g : IndexedGrammar T) (D : DFA T Q)
    {x : List (indexedDFAProduct g D).ISym}
    (h : (indexedDFAProduct g D).Transforms [.indexed none []] x) :
    ∃ q ∈ D.accept,
      x = [.indexed (some (D.start, g.initial, q)) []] := by
  rcases h with ⟨r, u, v, σ, hr, hsource, htarget⟩
  cases hc : r.consume with
  | none =>
      have hs : [.indexed none []] = u ++ [.indexed r.lhs σ] ++ v := by
        simpa [hc] using hsource
      rcases singleton_eq_append_singleton hs with ⟨rfl, rfl, hsym⟩
      injection hsym with hlhs hstack
      have hlhs' : r.lhs = none := hlhs.symm
      rcases product_rule_with_none_lhs g D r hr hlhs' with
        ⟨q, hq, hconsume, hrhs⟩
      refine ⟨q, hq, ?_⟩
      rw [hconsume] at hc
      simp only [List.nil_append, List.append_nil] at htarget
      rw [htarget, hrhs]
      subst σ
      rfl
  | some f =>
      have hs : [.indexed none []] = u ++ [.indexed r.lhs (f :: σ)] ++ v := by
        simpa [hc] using hsource
      rcases singleton_eq_append_singleton hs with ⟨_, _, hsym⟩
      injection hsym with _ hstack
      simp at hstack

private theorem indexedDFAProduct_language (g : IndexedGrammar T) (D : DFA T Q) :
    (indexedDFAProduct g D).Language = g.Language ⊓ D.accepts := by
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := IndexedGrammar.exists_derivesIn_of_derives hw
    cases n with
    | zero =>
        cases w <;> simp at hn
    | succ n =>
        have hsplit : (indexedDFAProduct g D).DerivesIn (1 + n)
            [.indexed none []]
            (w.map fun a => IndexedGrammar.ISym.terminal a) := by
          convert hn using 1 <;> omega
        rcases IndexedGrammar.derivesIn_split (m := 1) (n := n) hsplit with
          ⟨midForm, hfirst, hrest⟩
        rcases hfirst with ⟨before, hzero, hstep⟩
        simp at hzero
        subst before
        rcases product_initial_step g D hstep with ⟨q, hq, hmid⟩
        subst midForm
        rcases forward_key g D n D.start g.initial q [] w hrest with
          ⟨hg, heval⟩
        exact ⟨hg, by
          change D.evalFrom D.start w ∈ D.accept
          simpa [heval] using hq⟩
  · rintro ⟨hg, hD⟩
    obtain ⟨n, hn⟩ := IndexedGrammar.exists_derivesIn_of_derives hg
    change D.evalFrom D.start w ∈ D.accept at hD
    have hbody := backward_key g D n g.initial [] w D.start
      (D.evalFrom D.start w) hn rfl
    have hstartRule := product_start_rule_mem g D (D.evalFrom D.start w) hD
    apply IndexedGrammar.deri_of_tran_deri
    · refine ⟨(⟨none, none, [.nonterminal (some (D.start, g.initial,
            D.evalFrom D.start w)) none]⟩ :
          IRule T (ProductNT g Q) g.flag), [], [], [], hstartRule, ?_, rfl⟩
      simp [indexedDFAProduct]
    · simpa using hbody

private theorem Indexed_inter_regular {L R : Language T}
    (hL : is_Indexed L) (hR : R.IsRegular) : is_Indexed (L ⊓ R) := by
  rcases hL with ⟨g, rfl⟩
  rcases Language.isRegular_iff.mp hR with ⟨Q', instQ', D, rfl⟩
  letI : Fintype Q' := instQ'
  exact ⟨indexedDFAProduct g D, indexedDFAProduct_language g D⟩

private theorem Indexed_fInv {α β : Type} [Fintype α] [Fintype β]
    (L : Language β) (hL : is_Indexed L) :
    is_Indexed (fInv L : Language (α ⊕ β)) := by
  rw [fInv_eq]
  apply Indexed_closedUnderConcatenation
  · apply Indexed_closedUnderSubstitution L (substFn α β) hL
    intro b
    apply Indexed_closedUnderConcatenation
    · apply Indexed_closedUnderKleeneStar
      exact is_Indexed_of_is_CF is_CF_sLang
    · simpa [singletonWordLanguage] using
        (singletonWordLanguage_is_Indexed (T := α ⊕ β) [Sum.inr b])
  · apply Indexed_closedUnderKleeneStar
    exact is_Indexed_of_is_CF is_CF_sLang

/-- Indexed languages are closed under inverse string homomorphism. -/
public theorem Indexed_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_Indexed := by
  intro α β _ _ L h hL
  have hInv : is_Indexed (L.inverseHomomorphicImage h) := by
    rw [inverseHomomorphicImage_eq]
    apply Indexed_closedUnderHomomorphism
    apply Indexed_inter_regular
    · exact Indexed_fInv L hL
    · exact isRegular_dLang h
  simpa [Language.inverseHomomorphicImage, extendHom] using hInv

end
