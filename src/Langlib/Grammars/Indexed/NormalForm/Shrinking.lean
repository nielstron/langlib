module

public import Langlib.Grammars.Indexed.Basics.Higman
public import Langlib.Grammars.Indexed.NormalForm.Bounds
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Fintype.Prod
@[expose]
public section

/-!
# Shrinking infrastructure for indexed normal form

Higman's lemma supplies the stack-side finiteness used by shrinking arguments: for a fixed
nonterminal and target word, the stacks that can generate that word have finitely many minimal
representatives under the sublist order.
-/

variable {T : Type}

open List

namespace IndexedGrammar

/-- For a fixed nonterminal and terminal word, the minimal stacks that generate that word are
finite under the sublist order. -/
theorem finite_minimal_stacks_generating_word {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (w : List T) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          g.Derives [ISym.indexed A σ]
            (w.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      g.Derives [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym))}

/-- The minimal stacks generating a fixed word have a finite height bound. -/
theorem exists_bound_minimal_stacks_generating_word {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (w : List T) :
    ∃ B : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            g.Derives [ISym.indexed A τ]
              (w.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ B := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        g.Derives [ISym.indexed A τ]
          (w.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite := finite_minimal_stacks_generating_word (g := g) A w
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- Every stack that generates a fixed word has a sublist-minimal generating substack. -/
theorem exists_minimal_generating_substack {g : IndexedGrammar T}
    [Fintype g.flag] {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ τ : List g.flag,
      g.Derives [ISym.indexed A τ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      τ <+ σ ∧
      ∀ ρ : List g.flag,
        g.Derives [ISym.indexed A ρ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
  let Y : Set (List g.flag) :=
    {τ | g.Derives [ISym.indexed A τ]
      (w.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hsub⟩ := exists_minimal_sublist g.flag Y σ hder
  exact ⟨τ, hτmin.1, hsub, hτmin.2⟩

/-- For a fixed nonterminal and word, every generating stack can be shrunk to a generating
substack whose length is bounded uniformly over all original stacks. -/
theorem exists_bound_generating_substack {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (w : List T) :
    ∃ B : ℕ,
      ∀ σ : List g.flag,
        g.Derives [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ τ : List g.flag,
          g.Derives [ISym.indexed A τ]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ B ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed A ρ]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨B, hB⟩ := exists_bound_minimal_stacks_generating_word (g := g) A w
  refine ⟨B, ?_⟩
  intro σ hder
  obtain ⟨τ, hτ, hsub, hmin⟩ :=
    exists_minimal_generating_substack (g := g) (A := A) (σ := σ) (w := w) hder
  refine ⟨τ, hτ, hsub, ?_, hmin⟩
  exact hB τ ⟨hτ, hmin⟩

/-- A finite list of target words has one stack-shrinking bound for a fixed nonterminal. -/
theorem exists_bound_generating_substack_for_word_list {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (ws : List (List T)) :
    ∃ B : ℕ,
      ∀ w ∈ ws,
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A σ]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A τ]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ B ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A ρ]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction ws with
  | nil =>
      exact ⟨0, by simp⟩
  | cons w ws ih =>
      obtain ⟨Bw, hBw⟩ := exists_bound_generating_substack (g := g) A w
      obtain ⟨Bws, hBws⟩ := ih
      refine ⟨max Bw Bws, ?_⟩
      intro v hv σ hder
      rcases List.mem_cons.mp hv with rfl | hv'
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hBw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left Bw Bws), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hBws v hv' σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right Bw Bws), hmin⟩

/-- A finite list of nonterminals and target words has one stack-shrinking bound. -/
theorem exists_bound_generating_substack_for_nt_word_lists {g : IndexedGrammar T}
    [Fintype g.flag] (nts : List g.nt) (ws : List (List T)) :
    ∃ B : ℕ,
      ∀ A ∈ nts,
        ∀ w ∈ ws,
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A σ]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A τ]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ B ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction nts with
  | nil =>
      exact ⟨0, by simp⟩
  | cons A nts ih =>
      obtain ⟨BA, hBA⟩ := exists_bound_generating_substack_for_word_list (g := g) A ws
      obtain ⟨Bnts, hBnts⟩ := ih
      refine ⟨max BA Bnts, ?_⟩
      intro C hC w hw σ hder
      rcases List.mem_cons.mp hC with rfl | hC'
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hBA w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left BA Bnts), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hBnts C hC' w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right BA Bnts), hmin⟩

/-- Uniform stack-shrinking bound for all nonterminals and all sublists of a fixed target word.
The sublist family is a finite over-approximation of the terminal yields that recursive
subderivations can be asked to generate. -/
theorem exists_bound_generating_substack_for_target_sublists {g : IndexedGrammar T}
    [Fintype g.nt] [Fintype g.flag] (target : List T) :
    ∃ B : ℕ,
      ∀ A : g.nt, ∀ w : List T,
        w <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A σ]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A τ]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ B ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A ρ]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let nts : List g.nt := (Finset.univ : Finset g.nt).toList
  let ws : List (List T) := target.sublists
  obtain ⟨B, hB⟩ := exists_bound_generating_substack_for_nt_word_lists
    (g := g) nts ws
  refine ⟨B, ?_⟩
  intro A w hw σ hder
  exact hB A (by simp [nts]) w (by simpa [ws] using (List.mem_sublists).2 hw) σ hder

/-! ## Common inherited-stack shrinking for binary branches -/

/-- For fixed child nonterminals and fixed child yields, the sublist-minimal stacks that
generate both yields are finite. This is the binary-rule version of
`finite_minimal_stacks_generating_word`: the shared inherited stack is shrunk while preserving
both child subderivations. -/
theorem finite_minimal_stacks_generating_pair {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (u v : List T) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          g.Derives [ISym.indexed A σ]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C σ]
              (v.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      g.Derives [ISym.indexed A σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed C σ]
          (v.map fun a => (ISym.terminal a : g.ISym))}

/-- The common minimal stacks generating two fixed child yields have a finite height bound. -/
theorem exists_bound_minimal_stacks_generating_pair {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (u v : List T) :
    ∃ B : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            g.Derives [ISym.indexed A τ]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C τ]
                (v.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ B := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        g.Derives [ISym.indexed A τ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C τ]
            (v.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite := finite_minimal_stacks_generating_pair (g := g) A C u v
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- If one stack generates both child yields, it has a sublist-minimal common generating
substack. -/
theorem exists_minimal_generating_pair_substack {g : IndexedGrammar T}
    [Fintype g.flag] {A C : g.nt} {σ : List g.flag} {u v : List T}
    (hleft : g.Derives [ISym.indexed A σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ τ : List g.flag,
      g.Derives [ISym.indexed A τ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
      g.Derives [ISym.indexed C τ]
          (v.map fun a => (ISym.terminal a : g.ISym)) ∧
      τ <+ σ ∧
      ∀ ρ : List g.flag,
        g.Derives [ISym.indexed A ρ]
            (u.map fun a => (ISym.terminal a : g.ISym)) →
        g.Derives [ISym.indexed C ρ]
            (v.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
  let Y : Set (List g.flag) :=
    {τ | g.Derives [ISym.indexed A τ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed C τ]
          (v.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hsub⟩ :=
    exists_minimal_sublist g.flag Y σ ⟨hleft, hright⟩
  exact ⟨τ, hτmin.1.1, hτmin.1.2, hsub,
    fun ρ hρleft hρright hρsub => hτmin.2 ρ ⟨hρleft, hρright⟩ hρsub⟩

/-- For fixed child nonterminals and yields, every common generating stack can be shrunk to
a common generating substack whose length is bounded uniformly over all original stacks. -/
theorem exists_bound_generating_pair_substack {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (u v : List T) :
    ∃ B : ℕ,
      ∀ σ : List g.flag,
        g.Derives [ISym.indexed A σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) →
        g.Derives [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ τ : List g.flag,
          g.Derives [ISym.indexed A τ]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C τ]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ B ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed A ρ]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C ρ]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨B, hB⟩ := exists_bound_minimal_stacks_generating_pair (g := g) A C u v
  refine ⟨B, ?_⟩
  intro σ hleft hright
  obtain ⟨τ, hτleft, hτright, hsub, hmin⟩ :=
    exists_minimal_generating_pair_substack (g := g)
      (A := A) (C := C) (σ := σ) (u := u) (v := v) hleft hright
  refine ⟨τ, hτleft, hτright, hsub, ?_, hmin⟩
  exact hB τ ⟨⟨hτleft, hτright⟩,
    fun ρ hρ hρsub => hmin ρ hρ.1 hρ.2 hρsub⟩

/-- A finite right-yield list has one common stack-shrinking bound for fixed child
nonterminals and fixed left yield. -/
theorem exists_bound_generating_pair_substack_for_right_word_list {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (u : List T) (vs : List (List T)) :
    ∃ B : ℕ,
      ∀ v ∈ vs,
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A σ]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
          g.Derives [ISym.indexed C σ]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A τ]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C τ]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ B ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A ρ]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C ρ]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction vs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons v vs ih =>
      obtain ⟨Bv, hBv⟩ := exists_bound_generating_pair_substack (g := g) A C u v
      obtain ⟨Bvs, hBvs⟩ := ih
      refine ⟨max Bv Bvs, ?_⟩
      intro v' hv' σ hleft hright
      rcases List.mem_cons.mp hv' with rfl | hv_tail
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ := hBv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_left Bv Bvs),
          hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hBvs v' hv_tail σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_right Bv Bvs),
          hmin⟩

/-- A finite pair of child-yield lists has one common stack-shrinking bound for fixed child
nonterminals. -/
theorem exists_bound_generating_pair_substack_for_word_lists {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (us vs : List (List T)) :
    ∃ B : ℕ,
      ∀ u ∈ us,
        ∀ v ∈ vs,
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A σ]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C σ]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A τ]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C τ]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ B ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A ρ]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.Derives [ISym.indexed C ρ]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction us with
  | nil =>
      exact ⟨0, by simp⟩
  | cons u us ih =>
      obtain ⟨Bu, hBu⟩ :=
        exists_bound_generating_pair_substack_for_right_word_list (g := g) A C u vs
      obtain ⟨Bus, hBus⟩ := ih
      refine ⟨max Bu Bus, ?_⟩
      intro u' hu' v hv σ hleft hright
      rcases List.mem_cons.mp hu' with rfl | hu_tail
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hBu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_left Bu Bus),
          hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hBus u' hu_tail v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_right Bu Bus),
          hmin⟩

/-- A finite list of child-nonterminal pairs and target words has one common
stack-shrinking bound. -/
theorem exists_bound_generating_pair_substack_for_nt_pair_word_lists {g : IndexedGrammar T}
    [Fintype g.flag] (pairs : List (g.nt × g.nt)) (ws : List (List T)) :
    ∃ B : ℕ,
      ∀ A C, (A, C) ∈ pairs →
        ∀ u ∈ ws,
          ∀ v ∈ ws,
            ∀ σ : List g.flag,
              g.Derives [ISym.indexed A σ]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C σ]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ∃ τ : List g.flag,
                g.Derives [ISym.indexed A τ]
                    (u.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.Derives [ISym.indexed C τ]
                    (v.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧
                τ.length ≤ B ∧
                ∀ ρ : List g.flag,
                  g.Derives [ISym.indexed A ρ]
                      (u.map fun a => (ISym.terminal a : g.ISym)) →
                  g.Derives [ISym.indexed C ρ]
                      (v.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  induction pairs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pair pairs ih =>
      obtain ⟨Bpair, hBpair⟩ :=
        exists_bound_generating_pair_substack_for_word_lists (g := g) pair.1 pair.2 ws ws
      obtain ⟨Btail, hBtail⟩ := ih
      refine ⟨max Bpair Btail, ?_⟩
      intro A C hpair u hu v hv σ hleft hright
      rcases List.mem_cons.mp hpair with hhead | htail
      · have hA : A = pair.1 := by simpa using congrArg Prod.fst hhead
        have hC : C = pair.2 := by simpa using congrArg Prod.snd hhead
        subst A
        subst C
        obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hBpair u hu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub,
          le_trans hlen (Nat.le_max_left Bpair Btail), hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hBtail A C htail u hu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub,
          le_trans hlen (Nat.le_max_right Bpair Btail), hmin⟩

/-- Uniform common inherited-stack shrinking bound for every pair of nonterminals and every
pair of target sublists. This is the stack-side fact needed by binary normal-form branches:
if one inherited stack can generate both child yields, then a bounded common substack can
generate both child yields. -/
theorem exists_bound_generating_pair_substack_for_target_sublists {g : IndexedGrammar T}
    [Fintype g.nt] [Fintype g.flag] (target : List T) :
    ∃ B : ℕ,
      ∀ A C : g.nt, ∀ u v : List T,
        u <+ target →
        v <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A σ]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
          g.Derives [ISym.indexed C σ]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A τ]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C τ]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ B ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A ρ]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C ρ]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let pairs : List (g.nt × g.nt) := (Finset.univ : Finset (g.nt × g.nt)).toList
  let ws : List (List T) := target.sublists
  obtain ⟨B, hB⟩ := exists_bound_generating_pair_substack_for_nt_pair_word_lists
    (g := g) pairs ws
  refine ⟨B, ?_⟩
  intro A C u v hu hv σ hleft hright
  exact hB A C (by simp [pairs]) u
    (by simpa [ws] using (List.mem_sublists).2 hu) v
    (by simpa [ws] using (List.mem_sublists).2 hv) σ hleft hright

/-! ## Push-rule base-stack shrinking -/

/-- For a fixed pushed child nonterminal, top flag, and terminal word, the sublist-minimal
base stacks that generate that word after the pushed flag are finite. This is the push-rule
preimage form needed to shrink `σ` while preserving derivability from `B (f :: σ)`. -/
theorem finite_minimal_base_stacks_generating_pushed_word {g : IndexedGrammar T}
    [Fintype g.flag] (B : g.nt) (f : g.flag) (w : List T) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          g.Derives [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      g.Derives [ISym.indexed B (f :: σ)]
        (w.map fun a => (ISym.terminal a : g.ISym))}

/-- The minimal base stacks for a fixed pushed child derivation have a finite height bound. -/
theorem exists_bound_minimal_base_stacks_generating_pushed_word {g : IndexedGrammar T}
    [Fintype g.flag] (B : g.nt) (f : g.flag) (w : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            g.Derives [ISym.indexed B (f :: τ)]
              (w.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ K := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        g.Derives [ISym.indexed B (f :: τ)]
          (w.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite :=
    finite_minimal_base_stacks_generating_pushed_word (g := g) B f w
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- Every pushed child derivation has a sublist-minimal base stack preserving the pushed
top flag and the generated terminal word. -/
theorem exists_minimal_generating_pushed_substack {g : IndexedGrammar T}
    [Fintype g.flag] {B : g.nt} {f : g.flag} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed B (f :: σ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ τ : List g.flag,
      g.Derives [ISym.indexed B (f :: τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      τ <+ σ ∧
      ∀ ρ : List g.flag,
        g.Derives [ISym.indexed B (f :: ρ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
  let Y : Set (List g.flag) :=
    {τ | g.Derives [ISym.indexed B (f :: τ)]
      (w.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hsub⟩ := exists_minimal_sublist g.flag Y σ hder
  exact ⟨τ, hτmin.1, hsub, hτmin.2⟩

/-- For a fixed pushed child nonterminal, flag, and word, every generating base stack can be
shrunk to a bounded generating base substack. -/
theorem exists_bound_generating_pushed_substack {g : IndexedGrammar T}
    [Fintype g.flag] (B : g.nt) (f : g.flag) (w : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        g.Derives [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ τ : List g.flag,
          g.Derives [ISym.indexed B (f :: τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ K ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B (f :: ρ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_base_stacks_generating_pushed_word (g := g) B f w
  refine ⟨K, ?_⟩
  intro σ hder
  obtain ⟨τ, hτ, hsub, hmin⟩ :=
    exists_minimal_generating_pushed_substack
      (g := g) (B := B) (f := f) (σ := σ) (w := w) hder
  refine ⟨τ, hτ, hsub, ?_, hmin⟩
  exact hK τ ⟨hτ, hmin⟩

/-- A finite list of target words has one pushed-base stack-shrinking bound for a fixed
child nonterminal and pushed flag. -/
theorem exists_bound_generating_pushed_substack_for_word_list {g : IndexedGrammar T}
    [Fintype g.flag] (B : g.nt) (f : g.flag) (ws : List (List T)) :
    ∃ K : ℕ,
      ∀ w ∈ ws,
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed B (f :: τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed B (f :: ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction ws with
  | nil =>
      exact ⟨0, by simp⟩
  | cons w ws ih =>
      obtain ⟨Kw, hKw⟩ := exists_bound_generating_pushed_substack (g := g) B f w
      obtain ⟨Kws, hKws⟩ := ih
      refine ⟨max Kw Kws, ?_⟩
      intro v hv σ hder
      rcases List.mem_cons.mp hv with rfl | hv'
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left Kw Kws), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKws v hv' σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right Kw Kws), hmin⟩

/-- A finite list of pushed child nonterminal/flag pairs and target words has one
pushed-base stack-shrinking bound. -/
theorem exists_bound_generating_pushed_substack_for_nt_flag_word_lists
    {g : IndexedGrammar T} [Fintype g.flag]
    (pairs : List (g.nt × g.flag)) (ws : List (List T)) :
    ∃ K : ℕ,
      ∀ B : g.nt, ∀ f : g.flag,
        (B, f) ∈ pairs →
        ∀ w ∈ ws,
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed B (f :: σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed B (f :: τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed B (f :: ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction pairs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pair pairs ih =>
      obtain ⟨Kpair, hKpair⟩ :=
        exists_bound_generating_pushed_substack_for_word_list
          (g := g) pair.1 pair.2 ws
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpair Ktail, ?_⟩
      intro B f hpair w hw σ hder
      rcases List.mem_cons.mp hpair with hhead | htail
      · have hB : B = pair.1 := by simpa using congrArg Prod.fst hhead
        have hf : f = pair.2 := by simpa using congrArg Prod.snd hhead
        subst B
        subst f
        obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKpair w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left Kpair Ktail), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ :=
          hKtail B f htail w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right Kpair Ktail), hmin⟩

/-- Uniform pushed-base stack shrinking bound for every child nonterminal, pushed flag, and
target sublist. This is the push-rule counterpart of
`exists_bound_generating_pair_substack_for_target_sublists`: if `B (f :: σ)` generates a
target sublist, then the base stack `σ` can be shrunk uniformly while the top flag `f` is
preserved. -/
theorem exists_bound_generating_pushed_substack_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] (target : List T) :
    ∃ K : ℕ,
      ∀ B : g.nt, ∀ f : g.flag, ∀ w : List T,
        w <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed B (f :: τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed B (f :: ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let pairs : List (g.nt × g.flag) := (Finset.univ : Finset (g.nt × g.flag)).toList
  let ws : List (List T) := target.sublists
  obtain ⟨K, hK⟩ := exists_bound_generating_pushed_substack_for_nt_flag_word_lists
    (g := g) pairs ws
  refine ⟨K, ?_⟩
  intro B f w hw σ hder
  exact hK B f (by simp [pairs]) w
    (by simpa [ws] using (List.mem_sublists).2 hw) σ hder

/-! ## Fixed-prefix suffix shrinking -/

/-- For a fixed stack prefix, nonterminal, and terminal word, the sublist-minimal suffixes
that preserve derivability from `A (pref ++ σ)` are finite. -/
theorem finite_minimal_suffixes_generating_prefixed_word {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (pref : List g.flag) (w : List T) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          g.Derives [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      g.Derives [ISym.indexed A (pref ++ σ)]
        (w.map fun a => (ISym.terminal a : g.ISym))}

/-- The minimal suffixes for a fixed stack prefix, nonterminal, and word have a finite
height bound. -/
theorem exists_bound_minimal_suffixes_generating_prefixed_word {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (pref : List g.flag) (w : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            g.Derives [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ K := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        g.Derives [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite :=
    finite_minimal_suffixes_generating_prefixed_word (g := g) A pref w
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- Every suffix preserving derivability below a fixed stack prefix has a sublist-minimal
suffix preserving the same prefixed derivation. -/
theorem exists_minimal_generating_prefixed_suffix {g : IndexedGrammar T}
    [Fintype g.flag] {A : g.nt} {pref σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A (pref ++ σ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ τ : List g.flag,
      g.Derives [ISym.indexed A (pref ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      τ <+ σ ∧
      ∀ ρ : List g.flag,
        g.Derives [ISym.indexed A (pref ++ ρ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
  let Y : Set (List g.flag) :=
    {τ | g.Derives [ISym.indexed A (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hsub⟩ := exists_minimal_sublist g.flag Y σ hder
  exact ⟨τ, hτmin.1, hsub, hτmin.2⟩

/-- For a fixed stack prefix, nonterminal, and word, every generating suffix can be shrunk to
a bounded generating suffix while preserving the prefix exactly. -/
theorem exists_bound_generating_prefixed_suffix {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (pref : List g.flag) (w : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        g.Derives [ISym.indexed A (pref ++ σ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ τ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ K ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ ρ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_suffixes_generating_prefixed_word (g := g) A pref w
  refine ⟨K, ?_⟩
  intro σ hder
  obtain ⟨τ, hτ, hsub, hmin⟩ :=
    exists_minimal_generating_prefixed_suffix
      (g := g) (A := A) (pref := pref) (σ := σ) (w := w) hder
  refine ⟨τ, hτ, hsub, ?_, hmin⟩
  exact hK τ ⟨hτ, hmin⟩

/-! ### Count-budgeted fixed-prefix suffix shrinking -/

/-- For a fixed prefix, nonterminal, word, and step budget, the sublist-minimal suffixes that
generate the word within that budget are finite. -/
theorem finite_minimal_budgeted_suffixes_generating_prefixed_word {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (pref : List g.flag) (w : List T) (N : ℕ) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          ∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      ∃ n : ℕ, n ≤ N ∧
        g.DerivesIn n [ISym.indexed A (pref ++ σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))}

/-- The budgeted minimal suffixes for a fixed prefix, nonterminal, and word have a finite
height bound. -/
theorem exists_bound_minimal_budgeted_suffixes_generating_prefixed_word
    {g : IndexedGrammar T} [Fintype g.flag]
    (A : g.nt) (pref : List g.flag) (w : List T) (N : ℕ) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            ∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ K := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        ∃ n : ℕ, n ≤ N ∧
          g.DerivesIn n [ISym.indexed A (pref ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite :=
    finite_minimal_budgeted_suffixes_generating_prefixed_word
      (g := g) A pref w N
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- Every suffix that generates a fixed word within a fixed step budget has a bounded
sub-suffix that still generates the word within the same budget. The chosen sub-suffix is
minimal among all suffixes satisfying that same budgeted counted-derivation predicate. -/
theorem exists_bound_budgeted_generating_prefixed_suffix
    {g : IndexedGrammar T} [Fintype g.flag]
    (A : g.nt) (pref : List g.flag) (w : List T) (N : ℕ) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        (∃ n : ℕ, n ≤ N ∧
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))) →
        ∃ τ : List g.flag, ∃ n : ℕ,
          n ≤ N ∧
          g.DerivesIn n [ISym.indexed A (pref ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ K ∧
          ∀ ρ : List g.flag, ∀ m : ℕ,
            m ≤ N →
            g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_budgeted_suffixes_generating_prefixed_word
      (g := g) A pref w N
  refine ⟨K, ?_⟩
  intro σ hσ
  let Y : Set (List g.flag) :=
    {τ : List g.flag |
      ∃ n : ℕ, n ≤ N ∧
        g.DerivesIn n [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hτsub⟩ := exists_minimal_sublist g.flag Y σ hσ
  rcases hτmin.1 with ⟨n, hnN, hτder⟩
  refine ⟨τ, n, hnN, hτder, hτsub, ?_, ?_⟩
  · exact hK τ hτmin
  · intro ρ m hmN hρder hρsub
    exact hτmin.2 ρ ⟨m, hmN, hρder⟩ hρsub

/-- A finite list of target words has one count-budgeted fixed-prefix suffix-shrinking bound
for one nonterminal. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_word_list
    {g : IndexedGrammar T} [Fintype g.flag]
    (A : g.nt) (pref : List g.flag) (ws : List (List T)) (N : ℕ) :
    ∃ K : ℕ,
      ∀ w ∈ ws,
        ∀ σ : List g.flag,
          (∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym))) →
          ∃ τ : List g.flag, ∃ n : ℕ,
            n ≤ N ∧
            g.DerivesIn n [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ m : ℕ,
              m ≤ N →
              g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction ws with
  | nil =>
      exact ⟨0, by simp⟩
  | cons w ws ih =>
      obtain ⟨Kw, hKw⟩ :=
        exists_bound_budgeted_generating_prefixed_suffix (g := g) A pref w N
      obtain ⟨Kws, hKws⟩ := ih
      refine ⟨max Kw Kws, ?_⟩
      intro v hv σ hder
      rcases List.mem_cons.mp hv with rfl | hv'
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ := hKw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_left Kw Kws), hτmin⟩
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ :=
          hKws v hv' σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_right Kw Kws), hτmin⟩

/-- A finite list of nonterminals and target words has one count-budgeted fixed-prefix
suffix-shrinking bound. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_nt_word_lists
    {g : IndexedGrammar T} [Fintype g.flag]
    (nts : List g.nt) (pref : List g.flag) (ws : List (List T)) (N : ℕ) :
    ∃ K : ℕ,
      ∀ A ∈ nts,
        ∀ w ∈ ws,
          ∀ σ : List g.flag,
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ n : ℕ,
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m : ℕ,
                m ≤ N →
                g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction nts with
  | nil =>
      exact ⟨0, by simp⟩
  | cons A nts ih =>
      obtain ⟨KA, hKA⟩ :=
        exists_bound_budgeted_generating_prefixed_suffix_for_word_list
          (g := g) A pref ws N
      obtain ⟨Knts, hKnts⟩ := ih
      refine ⟨max KA Knts, ?_⟩
      intro B hB w hw σ hder
      rcases List.mem_cons.mp hB with rfl | hB'
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ := hKA w hw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_left KA Knts), hτmin⟩
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ :=
          hKnts B hB' w hw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_right KA Knts), hτmin⟩

/-- Uniform count-budgeted suffix shrinking for all nonterminals and all sublists of a fixed
target word under one fixed stack prefix. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (pref : List g.flag) (target : List T) (N : ℕ) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ w : List T,
        w <+ target →
        ∀ σ : List g.flag,
          (∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym))) →
          ∃ τ : List g.flag, ∃ n : ℕ,
            n ≤ N ∧
            g.DerivesIn n [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ m : ℕ,
              m ≤ N →
              g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let nts : List g.nt := (Finset.univ : Finset g.nt).toList
  let ws : List (List T) := target.sublists
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_nt_word_lists
      (g := g) nts pref ws N
  refine ⟨K, ?_⟩
  intro A w hw σ hder
  exact hK A (by simp [nts]) w
    (by simpa [ws] using (List.mem_sublists).2 hw) σ hder

/-- A finite list of prefixes has one count-budgeted suffix-shrinking bound for all
nonterminals and target sublists. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_prefix_list_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (prefixes : List (List g.flag)) (target : List T) (N : ℕ) :
    ∃ K : ℕ,
      ∀ pref ∈ prefixes,
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ n : ℕ,
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m : ℕ,
                m ≤ N →
                g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction prefixes with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pref prefixes ih =>
      obtain ⟨Kpref, hKpref⟩ :=
        exists_bound_budgeted_generating_prefixed_suffix_for_target_sublists
          (g := g) pref target N
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpref Ktail, ?_⟩
      intro pref' hpref' A w hw σ hder
      rcases List.mem_cons.mp hpref' with rfl | hpref_tail
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ :=
          hKpref A w hw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_left Kpref Ktail), hτmin⟩
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ :=
          hKtail pref' hpref_tail A w hw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_right Kpref Ktail), hτmin⟩

/-- Uniform count-budgeted suffix shrinking for every live prefix of length at most `P`.
The step budget `N` is preserved by the shrunken derivation. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ n : ℕ,
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m : ℕ,
                m ≤ N →
                g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  have hprefixes :
      ({pref : List g.flag | pref.length ≤ P} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag P
  let prefixes : List (List g.flag) := (Set.Finite.toFinset hprefixes).toList
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_prefix_list_target_sublists
      (g := g) prefixes target N
  refine ⟨K, ?_⟩
  intro pref hpref A w hw σ hder
  have hprefFinset : pref ∈ Set.Finite.toFinset hprefixes := by
    rw [Set.Finite.mem_toFinset]
    exact hpref
  have hprefList : pref ∈ prefixes := by
    simpa [prefixes] using hprefFinset
  exact hK pref hprefList A w hw σ hder

/-- A finite list of step budgets has one bounded-prefix count-budgeted suffix-shrinking
bound. This is used to keep exact child budgets while still extracting one uniform bound for
all budgets below a fixed global limit. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_budget_list_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P : ℕ) (budgets : List ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ N ∈ budgets,
        ∀ pref : List g.flag,
          pref.length ≤ P →
          ∀ A : g.nt, ∀ w : List T,
            w <+ target →
            ∀ σ : List g.flag,
              (∃ n : ℕ, n ≤ N ∧
                g.DerivesIn n [ISym.indexed A (pref ++ σ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))) →
              ∃ τ : List g.flag, ∃ n : ℕ,
                n ≤ N ∧
                g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                ∀ ρ : List g.flag, ∀ m : ℕ,
                  m ≤ N →
                  g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  induction budgets with
  | nil =>
      exact ⟨0, by simp⟩
  | cons N budgets ih =>
      obtain ⟨KN, hKN⟩ :=
        exists_bound_budgeted_generating_prefixed_suffix_for_bounded_prefix_target_sublists
          (g := g) P N target
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max KN Ktail, ?_⟩
      intro M hM pref hpref A w hw σ hder
      rcases List.mem_cons.mp hM with rfl | hMtail
      · obtain ⟨τ, n, hnN, hτder, hτsub, hτlen, hτmin⟩ :=
          hKN pref hpref A w hw σ hder
        exact ⟨τ, n, hnN, hτder, hτsub,
          le_trans hτlen (Nat.le_max_left KN Ktail), hτmin⟩
      · obtain ⟨τ, n, hnM, hτder, hτsub, hτlen, hτmin⟩ :=
          hKtail M hMtail pref hpref A w hw σ hder
        exact ⟨τ, n, hnM, hτder, hτsub,
          le_trans hτlen (Nat.le_max_right KN Ktail), hτmin⟩

/-- Uniform bounded-prefix count-budgeted suffix shrinking for every step budget `M ≤ N`.
The returned counted derivation remains within the same budget `M`. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_budget_upto_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ M : ℕ,
        M ≤ N →
        ∀ pref : List g.flag,
          pref.length ≤ P →
          ∀ A : g.nt, ∀ w : List T,
            w <+ target →
            ∀ σ : List g.flag,
              (∃ n : ℕ, n ≤ M ∧
                g.DerivesIn n [ISym.indexed A (pref ++ σ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))) →
              ∃ τ : List g.flag, ∃ n : ℕ,
                n ≤ M ∧
                g.DerivesIn n [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                ∀ ρ : List g.flag, ∀ m : ℕ,
                  m ≤ M →
                  g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  let budgets : List ℕ := List.range (N + 1)
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_budget_list_bounded_prefix_target_sublists
      (g := g) P budgets target
  refine ⟨K, ?_⟩
  intro M hMN pref hpref A w hw σ hder
  have hMmem : M ∈ budgets := by
    simp [budgets, Nat.lt_succ_iff, hMN]
  exact hK M hMmem pref hpref A w hw σ hder

/-- Count-budgeted suffix shrinking under one combined live-prefix/step budget. The returned
derivation remains within the original local step budget `n`. -/
theorem exists_bound_budgeted_generating_prefixed_suffix_for_bounded_prefix_combined_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (Q : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ Q →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          pref.length + n ≤ Q →
          ∃ m : ℕ, ∃ τ : List g.flag,
            m ≤ n ∧
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ k : ℕ,
              k ≤ n →
              g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_budget_upto_bounded_prefix_target_sublists
      (g := g) Q Q target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hbudget
  have hnQ : n ≤ Q := by omega
  obtain ⟨τ, m, hm, hτder, hτsub, hτlen, hτmin⟩ :=
    hK n hnQ pref hpref A w hwt σ ⟨n, le_rfl, hder⟩
  refine ⟨m, τ, hm, hτder, hτsub, hτlen, ?_⟩
  intro ρ k hk hρder hρsub
  exact hτmin ρ k hk hρder hρsub

/-! ### Count-budgeted common fixed-prefix suffix shrinking -/

/-- For fixed child nonterminals, yields, prefix, and step budgets, the sublist-minimal common
suffixes preserving both counted child derivations within those budgets are finite. -/
theorem finite_minimal_budgeted_suffixes_generating_prefixed_pair
    {g : IndexedGrammar T} [Fintype g.flag]
    (A C : g.nt) (pref : List g.flag) (u v : List T) (M N : ℕ) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          (∃ m : ℕ, m ≤ M ∧
            g.DerivesIn m [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym))) ∧
          (∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym)))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      (∃ m : ℕ, m ≤ M ∧
        g.DerivesIn m [ISym.indexed A (pref ++ σ)]
          (u.map fun a => (ISym.terminal a : g.ISym))) ∧
      (∃ n : ℕ, n ≤ N ∧
        g.DerivesIn n [ISym.indexed C (pref ++ σ)]
          (v.map fun a => (ISym.terminal a : g.ISym)))}

/-- The budgeted common minimal suffixes for a fixed prefix and fixed child yields have a
finite height bound. -/
theorem exists_bound_minimal_budgeted_suffixes_generating_prefixed_pair
    {g : IndexedGrammar T} [Fintype g.flag]
    (A C : g.nt) (pref : List g.flag) (u v : List T) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            (∃ m : ℕ, m ≤ M ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym))) ∧
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)))} →
        σ.length ≤ K := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        (∃ m : ℕ, m ≤ M ∧
          g.DerivesIn m [ISym.indexed A (pref ++ τ)]
            (u.map fun a => (ISym.terminal a : g.ISym))) ∧
        (∃ n : ℕ, n ≤ N ∧
          g.DerivesIn n [ISym.indexed C (pref ++ τ)]
            (v.map fun a => (ISym.terminal a : g.ISym)))}
  have hS : S.Finite :=
    finite_minimal_budgeted_suffixes_generating_prefixed_pair
      (g := g) A C pref u v M N
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- Count-budgeted common suffix shrinking for a fixed prefix and fixed child yields. Both
child derivations are preserved within their original budgets. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix
    {g : IndexedGrammar T} [Fintype g.flag]
    (A C : g.nt) (pref : List g.flag) (u v : List T) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        (∃ m : ℕ, m ≤ M ∧
          g.DerivesIn m [ISym.indexed A (pref ++ σ)]
            (u.map fun a => (ISym.terminal a : g.ISym))) →
        (∃ n : ℕ, n ≤ N ∧
          g.DerivesIn n [ISym.indexed C (pref ++ σ)]
            (v.map fun a => (ISym.terminal a : g.ISym))) →
        ∃ τ : List g.flag, ∃ m n : ℕ,
          m ≤ M ∧ n ≤ N ∧
          g.DerivesIn m [ISym.indexed A (pref ++ τ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn n [ISym.indexed C (pref ++ τ)]
            (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          ∀ ρ : List g.flag, ∀ m' n' : ℕ,
            m' ≤ M →
            n' ≤ N →
            g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_budgeted_suffixes_generating_prefixed_pair
      (g := g) A C pref u v M N
  refine ⟨K, ?_⟩
  intro σ hleft hright
  let Y : Set (List g.flag) :=
    {τ : List g.flag |
      (∃ m : ℕ, m ≤ M ∧
        g.DerivesIn m [ISym.indexed A (pref ++ τ)]
          (u.map fun a => (ISym.terminal a : g.ISym))) ∧
      (∃ n : ℕ, n ≤ N ∧
        g.DerivesIn n [ISym.indexed C (pref ++ τ)]
          (v.map fun a => (ISym.terminal a : g.ISym)))}
  obtain ⟨τ, hτmin, hτsub⟩ := exists_minimal_sublist g.flag Y σ ⟨hleft, hright⟩
  rcases hτmin.1 with ⟨⟨m, hmM, hτleft⟩, ⟨n, hnN, hτright⟩⟩
  refine ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, ?_, ?_⟩
  · exact hK τ hτmin
  · intro ρ m' n' hm'M hn'N hρleft hρright hρsub
    exact hτmin.2 ρ ⟨⟨m', hm'M, hρleft⟩, ⟨n', hn'N, hρright⟩⟩ hρsub

/-- A finite right-yield list has one count-budgeted common suffix-shrinking bound for fixed
left yield and child nonterminals. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_right_word_list
    {g : IndexedGrammar T} [Fintype g.flag]
    (A C : g.nt) (pref : List g.flag) (u : List T) (vs : List (List T))
    (M N : ℕ) :
    ∃ K : ℕ,
      ∀ v ∈ vs,
        ∀ σ : List g.flag,
          (∃ m : ℕ, m ≤ M ∧
            g.DerivesIn m [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym))) →
          (∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym))) →
          ∃ τ : List g.flag, ∃ m n : ℕ,
            m ≤ M ∧ n ≤ N ∧
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn n [ISym.indexed C (pref ++ τ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ m' n' : ℕ,
              m' ≤ M →
              n' ≤ N →
              g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction vs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons v vs ih =>
      obtain ⟨Kv, hKv⟩ :=
        exists_bound_budgeted_generating_prefixed_pair_suffix
          (g := g) A C pref u v M N
      obtain ⟨Kvs, hKvs⟩ := ih
      refine ⟨max Kv Kvs, ?_⟩
      intro v' hv' σ hleft hright
      rcases List.mem_cons.mp hv' with rfl | hv_tail
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Kv Kvs), hτmin⟩
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKvs v' hv_tail σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Kv Kvs), hτmin⟩

/-- A finite pair of child-yield lists has one count-budgeted common suffix-shrinking bound
for fixed child nonterminals. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_word_lists
    {g : IndexedGrammar T} [Fintype g.flag]
    (A C : g.nt) (pref : List g.flag) (us vs : List (List T)) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ u ∈ us,
        ∀ v ∈ vs,
          ∀ σ : List g.flag,
            (∃ m : ℕ, m ≤ M ∧
              g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym))) →
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ m n : ℕ,
              m ≤ M ∧ n ≤ N ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                m' ≤ M →
                n' ≤ N →
                g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction us with
  | nil =>
      exact ⟨0, by simp⟩
  | cons u us ih =>
      obtain ⟨Ku, hKu⟩ :=
        exists_bound_budgeted_generating_prefixed_pair_suffix_for_right_word_list
          (g := g) A C pref u vs M N
      obtain ⟨Kus, hKus⟩ := ih
      refine ⟨max Ku Kus, ?_⟩
      intro u' hu' v hv σ hleft hright
      rcases List.mem_cons.mp hu' with rfl | hu_tail
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKu v hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Ku Kus), hτmin⟩
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKus u' hu_tail v hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Ku Kus), hτmin⟩

/-- A finite list of child-nonterminal pairs and target words has one count-budgeted common
suffix-shrinking bound. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_nt_pair_word_lists
    {g : IndexedGrammar T} [Fintype g.flag]
    (pairs : List (g.nt × g.nt)) (pref : List g.flag) (ws : List (List T)) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ A C, (A, C) ∈ pairs →
        ∀ u ∈ ws,
          ∀ v ∈ ws,
            ∀ σ : List g.flag,
              (∃ m : ℕ, m ≤ M ∧
                g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                  (u.map fun a => (ISym.terminal a : g.ISym))) →
              (∃ n : ℕ, n ≤ N ∧
                g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                  (v.map fun a => (ISym.terminal a : g.ISym))) →
              ∃ τ : List g.flag, ∃ m n : ℕ,
                m ≤ M ∧ n ≤ N ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                  m' ≤ M →
                  n' ≤ N →
                  g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                  g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  induction pairs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pair pairs ih =>
      obtain ⟨Kpair, hKpair⟩ :=
        exists_bound_budgeted_generating_prefixed_pair_suffix_for_word_lists
          (g := g) pair.1 pair.2 pref ws ws M N
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpair Ktail, ?_⟩
      intro A C hpair u hu v hv σ hleft hright
      rcases List.mem_cons.mp hpair with hhead | htail
      · subst pair
        obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKpair u hu v hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Kpair Ktail), hτmin⟩
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKtail A C htail u hu v hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Kpair Ktail), hτmin⟩

/-- Uniform count-budgeted common suffix shrinking for every pair of nonterminals and every
pair of target sublists under one fixed stack prefix. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (pref : List g.flag) (target : List T) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ A C : g.nt, ∀ u v : List T,
        u <+ target →
        v <+ target →
        ∀ σ : List g.flag,
          (∃ m : ℕ, m ≤ M ∧
            g.DerivesIn m [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym))) →
          (∃ n : ℕ, n ≤ N ∧
            g.DerivesIn n [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym))) →
          ∃ τ : List g.flag, ∃ m n : ℕ,
            m ≤ M ∧ n ≤ N ∧
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn n [ISym.indexed C (pref ++ τ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ m' n' : ℕ,
              m' ≤ M →
              n' ≤ N →
              g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let pairs : List (g.nt × g.nt) := (Finset.univ : Finset (g.nt × g.nt)).toList
  let ws : List (List T) := target.sublists
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_nt_pair_word_lists
      (g := g) pairs pref ws M N
  refine ⟨K, ?_⟩
  intro A C u v hu hv σ hleft hright
  exact hK A C (by simp [pairs]) u
    (by simpa [ws] using (List.mem_sublists).2 hu) v
    (by simpa [ws] using (List.mem_sublists).2 hv) σ hleft hright

/-- A finite prefix list has one count-budgeted common suffix-shrinking bound for all child
nonterminal pairs and target sublists. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_prefix_list_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (prefixes : List (List g.flag)) (target : List T) (M N : ℕ) :
    ∃ K : ℕ,
      ∀ pref ∈ prefixes,
        ∀ A C : g.nt, ∀ u v : List T,
          u <+ target →
          v <+ target →
          ∀ σ : List g.flag,
            (∃ m : ℕ, m ≤ M ∧
              g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym))) →
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ m n : ℕ,
              m ≤ M ∧ n ≤ N ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                m' ≤ M →
                n' ≤ N →
                g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction prefixes with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pref prefixes ih =>
      obtain ⟨Kpref, hKpref⟩ :=
        exists_bound_budgeted_generating_prefixed_pair_suffix_for_target_sublists
          (g := g) pref target M N
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpref Ktail, ?_⟩
      intro pref' hpref' A C u v hu hv σ hleft hright
      rcases List.mem_cons.mp hpref' with rfl | hpref_tail
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKpref A C u v hu hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Kpref Ktail), hτmin⟩
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKtail pref' hpref_tail A C u v hu hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Kpref Ktail), hτmin⟩

/-- Uniform count-budgeted common suffix shrinking for every live prefix of length at most
`P`. Both child step budgets are preserved. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P M N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ A C : g.nt, ∀ u v : List T,
          u <+ target →
          v <+ target →
          ∀ σ : List g.flag,
            (∃ m : ℕ, m ≤ M ∧
              g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym))) →
            (∃ n : ℕ, n ≤ N ∧
              g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym))) →
            ∃ τ : List g.flag, ∃ m n : ℕ,
              m ≤ M ∧ n ≤ N ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                m' ≤ M →
                n' ≤ N →
                g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  have hprefixes :
      ({pref : List g.flag | pref.length ≤ P} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag P
  let prefixes : List (List g.flag) := (Set.Finite.toFinset hprefixes).toList
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_prefix_list_target_sublists
      (g := g) prefixes target M N
  refine ⟨K, ?_⟩
  intro pref hpref A C u v hu hv σ hleft hright
  have hprefFinset : pref ∈ Set.Finite.toFinset hprefixes := by
    rw [Set.Finite.mem_toFinset]
    exact hpref
  have hprefList : pref ∈ prefixes := by
    simpa [prefixes] using hprefFinset
  exact hK pref hprefList A C u v hu hv σ hleft hright

/-- A finite list of child-budget pairs has one bounded-prefix count-budgeted common
suffix-shrinking bound. Each returned child derivation remains within its own supplied
budget. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_budget_pair_list_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P : ℕ) (budgets : List (ℕ × ℕ)) (target : List T) :
    ∃ K : ℕ,
      ∀ M N, (M, N) ∈ budgets →
        ∀ pref : List g.flag,
          pref.length ≤ P →
          ∀ A C : g.nt, ∀ u v : List T,
            u <+ target →
            v <+ target →
            ∀ σ : List g.flag,
              (∃ m : ℕ, m ≤ M ∧
                g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                  (u.map fun a => (ISym.terminal a : g.ISym))) →
              (∃ n : ℕ, n ≤ N ∧
                g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                  (v.map fun a => (ISym.terminal a : g.ISym))) →
              ∃ τ : List g.flag, ∃ m n : ℕ,
                m ≤ M ∧ n ≤ N ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                  m' ≤ M →
                  n' ≤ N →
                  g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                  g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  induction budgets with
  | nil =>
      exact ⟨0, by simp⟩
  | cons budget budgets ih =>
      obtain ⟨Kbudget, hKbudget⟩ :=
        exists_bound_budgeted_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
          (g := g) P budget.1 budget.2 target
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kbudget Ktail, ?_⟩
      intro M N hbudget pref hpref A C u v hu hv σ hleft hright
      rcases List.mem_cons.mp hbudget with hhead | htail
      · subst budget
        obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKbudget pref hpref A C u v hu hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Kbudget Ktail), hτmin⟩
      · obtain ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKtail M N htail pref hpref A C u v hu hv σ hleft hright
        exact ⟨τ, m, n, hmM, hnN, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Kbudget Ktail), hτmin⟩

/-- Uniform bounded-prefix count-budgeted common suffix shrinking for all child-budget pairs
`M, N ≤ B`. Each returned child derivation remains within its own original budget. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_budget_upto_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (P B : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ M N : ℕ,
        M ≤ B →
        N ≤ B →
        ∀ pref : List g.flag,
          pref.length ≤ P →
          ∀ A C : g.nt, ∀ u v : List T,
            u <+ target →
            v <+ target →
            ∀ σ : List g.flag,
              (∃ m : ℕ, m ≤ M ∧
                g.DerivesIn m [ISym.indexed A (pref ++ σ)]
                  (u.map fun a => (ISym.terminal a : g.ISym))) →
              (∃ n : ℕ, n ≤ N ∧
                g.DerivesIn n [ISym.indexed C (pref ++ σ)]
                  (v.map fun a => (ISym.terminal a : g.ISym))) →
              ∃ τ : List g.flag, ∃ m n : ℕ,
                m ≤ M ∧ n ≤ N ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                ∀ ρ : List g.flag, ∀ m' n' : ℕ,
                  m' ≤ M →
                  n' ≤ N →
                  g.DerivesIn m' [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                  g.DerivesIn n' [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  let budgets : List (ℕ × ℕ) :=
    (List.range (B + 1)).flatMap fun M =>
      (List.range (B + 1)).map fun N => (M, N)
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_budget_pair_list_bounded_prefix_target_sublists
      (g := g) P budgets target
  refine ⟨K, ?_⟩
  intro M N hMB hNB pref hpref A C u v hu hv σ hleft hright
  have hbudgetMem : (M, N) ∈ budgets := by
    simp [budgets, Nat.lt_succ_iff, hMB, hNB]
  exact hK M N hbudgetMem pref hpref A C u v hu hv σ hleft hright

/-- Count-budgeted common suffix shrinking under one combined live-prefix/child-step budget.
Both returned child derivations remain within their original local budgets. -/
theorem exists_bound_budgeted_generating_prefixed_pair_suffix_for_bounded_prefix_combined_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (Q : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ Q →
        ∀ m k : ℕ, ∀ A C : g.nt, ∀ u v : List T, ∀ σ : List g.flag,
          u <+ target →
          v <+ target →
          g.DerivesIn m [ISym.indexed A (pref ++ σ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) →
          g.DerivesIn k [ISym.indexed C (pref ++ σ)]
            (v.map fun a => (ISym.terminal a : g.ISym)) →
          pref.length + (m + k) ≤ Q →
          ∃ m' k' : ℕ, ∃ τ : List g.flag,
            m' ≤ m ∧ k' ≤ k ∧ m' + k' ≤ m + k ∧
            g.DerivesIn m' [ISym.indexed A (pref ++ τ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn k' [ISym.indexed C (pref ++ τ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ m'' k'' : ℕ,
              m'' ≤ m →
              k'' ≤ k →
              g.DerivesIn m'' [ISym.indexed A (pref ++ ρ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.DerivesIn k'' [ISym.indexed C (pref ++ ρ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_budget_upto_bounded_prefix_target_sublists
      (g := g) Q Q target
  refine ⟨K, ?_⟩
  intro pref hpref m k A C u v σ hu hv hleft hright hbudget
  have hmQ : m ≤ Q := by omega
  have hkQ : k ≤ Q := by omega
  obtain ⟨τ, m', k', hm', hk', hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
    hK m k hmQ hkQ pref hpref A C u v hu hv σ
      ⟨m, le_rfl, hleft⟩ ⟨k, le_rfl, hright⟩
  refine ⟨m', k', τ, hm', hk', by omega, hτleft, hτright, hτsub, hτlen, ?_⟩
  intro ρ m'' k'' hm'' hk'' hρleft hρright hρsub
  exact hτmin ρ m'' k'' hm'' hk'' hρleft hρright hρsub

/-- A finite list of target words has one fixed-prefix suffix-shrinking bound for one
nonterminal. -/
theorem exists_bound_generating_prefixed_suffix_for_word_list {g : IndexedGrammar T}
    [Fintype g.flag] (A : g.nt) (pref : List g.flag) (ws : List (List T)) :
    ∃ K : ℕ,
      ∀ w ∈ ws,
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction ws with
  | nil =>
      exact ⟨0, by simp⟩
  | cons w ws ih =>
      obtain ⟨Kw, hKw⟩ :=
        exists_bound_generating_prefixed_suffix (g := g) A pref w
      obtain ⟨Kws, hKws⟩ := ih
      refine ⟨max Kw Kws, ?_⟩
      intro v hv σ hder
      rcases List.mem_cons.mp hv with rfl | hv'
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left Kw Kws), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKws v hv' σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right Kw Kws), hmin⟩

/-- A finite list of nonterminals and target words has one fixed-prefix suffix-shrinking
bound. -/
theorem exists_bound_generating_prefixed_suffix_for_nt_word_lists {g : IndexedGrammar T}
    [Fintype g.flag] (nts : List g.nt) (pref : List g.flag) (ws : List (List T)) :
    ∃ K : ℕ,
      ∀ A ∈ nts,
        ∀ w ∈ ws,
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction nts with
  | nil =>
      exact ⟨0, by simp⟩
  | cons A nts ih =>
      obtain ⟨KA, hKA⟩ :=
        exists_bound_generating_prefixed_suffix_for_word_list (g := g) A pref ws
      obtain ⟨Knts, hKnts⟩ := ih
      refine ⟨max KA Knts, ?_⟩
      intro C hC w hw σ hder
      rcases List.mem_cons.mp hC with rfl | hC'
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKA w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_left KA Knts), hmin⟩
      · obtain ⟨τ, hτ, hsub, hlen, hmin⟩ := hKnts C hC' w hw σ hder
        exact ⟨τ, hτ, hsub, le_trans hlen (Nat.le_max_right KA Knts), hmin⟩

/-- Uniform suffix shrinking for all nonterminals and target sublists under one fixed stack
prefix. -/
theorem exists_bound_generating_prefixed_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (pref : List g.flag) (target : List T) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ w : List T,
        w <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let nts : List g.nt := (Finset.univ : Finset g.nt).toList
  let ws : List (List T) := target.sublists
  obtain ⟨K, hK⟩ := exists_bound_generating_prefixed_suffix_for_nt_word_lists
    (g := g) nts pref ws
  refine ⟨K, ?_⟩
  intro A w hw σ hder
  exact hK A (by simp [nts]) w
    (by simpa [ws] using (List.mem_sublists).2 hw) σ hder

/-- For a fixed stack prefix, child nonterminals, and child yields, the sublist-minimal
suffixes that preserve both prefixed child derivations are finite. -/
theorem finite_minimal_suffixes_generating_prefixed_pair {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (pref : List g.flag) (u v : List T) :
    Set.Finite
      (minimalElements g.flag
        {σ : List g.flag |
          g.Derives [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym))}) :=
  higman_finite_antichain g.flag
    {σ : List g.flag |
      g.Derives [ISym.indexed A (pref ++ σ)]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed C (pref ++ σ)]
          (v.map fun a => (ISym.terminal a : g.ISym))}

/-- The common minimal suffixes preserving two fixed prefixed child derivations have a finite
height bound. -/
theorem exists_bound_minimal_suffixes_generating_prefixed_pair {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (pref : List g.flag) (u v : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        σ ∈ minimalElements g.flag
          {τ : List g.flag |
            g.Derives [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym))} →
        σ.length ≤ K := by
  let S : Set (List g.flag) :=
    minimalElements g.flag
      {τ : List g.flag |
        g.Derives [ISym.indexed A (pref ++ τ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C (pref ++ τ)]
            (v.map fun a => (ISym.terminal a : g.ISym))}
  have hS : S.Finite :=
    finite_minimal_suffixes_generating_prefixed_pair (g := g) A C pref u v
  refine ⟨(Set.Finite.toFinset hS).sup List.length, ?_⟩
  intro σ hσ
  exact Finset.le_sup (s := Set.Finite.toFinset hS) (f := List.length)
    (by
      rw [Set.Finite.mem_toFinset]
      exact hσ)

/-- If one suffix preserves both child yields under a fixed prefix, it has a sublist-minimal
common suffix preserving both prefixed child derivations. -/
theorem exists_minimal_generating_prefixed_pair_suffix {g : IndexedGrammar T}
    [Fintype g.flag] {A C : g.nt} {pref σ : List g.flag} {u v : List T}
    (hleft : g.Derives [ISym.indexed A (pref ++ σ)]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C (pref ++ σ)]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ τ : List g.flag,
      g.Derives [ISym.indexed A (pref ++ τ)]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
      g.Derives [ISym.indexed C (pref ++ τ)]
          (v.map fun a => (ISym.terminal a : g.ISym)) ∧
      τ <+ σ ∧
      ∀ ρ : List g.flag,
        g.Derives [ISym.indexed A (pref ++ ρ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) →
        g.Derives [ISym.indexed C (pref ++ ρ)]
            (v.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
  let Y : Set (List g.flag) :=
    {τ | g.Derives [ISym.indexed A (pref ++ τ)]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed C (pref ++ τ)]
          (v.map fun a => (ISym.terminal a : g.ISym))}
  obtain ⟨τ, hτmin, hsub⟩ :=
    exists_minimal_sublist g.flag Y σ ⟨hleft, hright⟩
  exact ⟨τ, hτmin.1.1, hτmin.1.2, hsub,
    fun ρ hρleft hρright hρsub => hτmin.2 ρ ⟨hρleft, hρright⟩ hρsub⟩

/-- For fixed child nonterminals, yields, and stack prefix, every common generating suffix can
be shrunk to a bounded common generating suffix. -/
theorem exists_bound_generating_prefixed_pair_suffix {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (pref : List g.flag) (u v : List T) :
    ∃ K : ℕ,
      ∀ σ : List g.flag,
        g.Derives [ISym.indexed A (pref ++ σ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) →
        g.Derives [ISym.indexed C (pref ++ σ)]
            (v.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ τ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ τ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C (pref ++ τ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          τ <+ σ ∧
          τ.length ≤ K ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ ρ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C (pref ++ ρ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_suffixes_generating_prefixed_pair (g := g) A C pref u v
  refine ⟨K, ?_⟩
  intro σ hleft hright
  obtain ⟨τ, hτleft, hτright, hsub, hmin⟩ :=
    exists_minimal_generating_prefixed_pair_suffix
      (g := g) (A := A) (C := C) (pref := pref) (σ := σ)
      (u := u) (v := v) hleft hright
  refine ⟨τ, hτleft, hτright, hsub, ?_, hmin⟩
  exact hK τ ⟨⟨hτleft, hτright⟩,
    fun ρ hρ hρsub => hmin ρ hρ.1 hρ.2 hρsub⟩

/-- A finite right-yield list has one fixed-prefix common suffix-shrinking bound for fixed
child nonterminals and fixed left yield. -/
theorem exists_bound_generating_prefixed_pair_suffix_for_right_word_list
    {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (pref : List g.flag) (u : List T)
    (vs : List (List T)) :
    ∃ K : ℕ,
      ∀ v ∈ vs,
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
          g.Derives [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  induction vs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons v vs ih =>
      obtain ⟨Kv, hKv⟩ :=
        exists_bound_generating_prefixed_pair_suffix (g := g) A C pref u v
      obtain ⟨Kvs, hKvs⟩ := ih
      refine ⟨max Kv Kvs, ?_⟩
      intro v' hv' σ hleft hright
      rcases List.mem_cons.mp hv' with rfl | hv_tail
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ := hKv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_left Kv Kvs),
          hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hKvs v' hv_tail σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_right Kv Kvs),
          hmin⟩

/-- A finite pair of child-yield lists has one fixed-prefix common suffix-shrinking bound for
fixed child nonterminals. -/
theorem exists_bound_generating_prefixed_pair_suffix_for_word_lists
    {g : IndexedGrammar T}
    [Fintype g.flag] (A C : g.nt) (pref : List g.flag)
    (us vs : List (List T)) :
    ∃ K : ℕ,
      ∀ u ∈ us,
        ∀ v ∈ vs,
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.Derives [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction us with
  | nil =>
      exact ⟨0, by simp⟩
  | cons u us ih =>
      obtain ⟨Ku, hKu⟩ :=
        exists_bound_generating_prefixed_pair_suffix_for_right_word_list
          (g := g) A C pref u vs
      obtain ⟨Kus, hKus⟩ := ih
      refine ⟨max Ku Kus, ?_⟩
      intro u' hu' v hv σ hleft hright
      rcases List.mem_cons.mp hu' with rfl | hu_tail
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hKu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_left Ku Kus),
          hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hKus u' hu_tail v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub, le_trans hlen (Nat.le_max_right Ku Kus),
          hmin⟩

/-- A finite list of child-nonterminal pairs and target words has one fixed-prefix common
suffix-shrinking bound. -/
theorem exists_bound_generating_prefixed_pair_suffix_for_nt_pair_word_lists
    {g : IndexedGrammar T}
    [Fintype g.flag] (pairs : List (g.nt × g.nt)) (pref : List g.flag)
    (ws : List (List T)) :
    ∃ K : ℕ,
      ∀ A C, (A, C) ∈ pairs →
        ∀ u ∈ ws,
          ∀ v ∈ ws,
            ∀ σ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ σ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C (pref ++ σ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ∃ τ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ τ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.Derives [ISym.indexed C (pref ++ τ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧
                τ.length ≤ K ∧
                ∀ ρ : List g.flag,
                  g.Derives [ISym.indexed A (pref ++ ρ)]
                      (u.map fun a => (ISym.terminal a : g.ISym)) →
                  g.Derives [ISym.indexed C (pref ++ ρ)]
                      (v.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  induction pairs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pair pairs ih =>
      obtain ⟨Kpair, hKpair⟩ :=
        exists_bound_generating_prefixed_pair_suffix_for_word_lists
          (g := g) pair.1 pair.2 pref ws ws
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpair Ktail, ?_⟩
      intro A C hpair u hu v hv σ hleft hright
      rcases List.mem_cons.mp hpair with hhead | htail
      · have hA : A = pair.1 := by simpa using congrArg Prod.fst hhead
        have hC : C = pair.2 := by simpa using congrArg Prod.snd hhead
        subst A
        subst C
        obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hKpair u hu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub,
          le_trans hlen (Nat.le_max_left Kpair Ktail), hmin⟩
      · obtain ⟨τ, hτleft, hτright, hsub, hlen, hmin⟩ :=
          hKtail A C htail u hu v hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hsub,
          le_trans hlen (Nat.le_max_right Kpair Ktail), hmin⟩

/-- Uniform common suffix shrinking for every pair of nonterminals and every pair of target
sublists under one fixed stack prefix. -/
theorem exists_bound_generating_prefixed_pair_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (pref : List g.flag) (target : List T) :
    ∃ K : ℕ,
      ∀ A C : g.nt, ∀ u v : List T,
        u <+ target →
        v <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A (pref ++ σ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
          g.Derives [ISym.indexed C (pref ++ σ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let pairs : List (g.nt × g.nt) := (Finset.univ : Finset (g.nt × g.nt)).toList
  let ws : List (List T) := target.sublists
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_pair_suffix_for_nt_pair_word_lists
      (g := g) pairs pref ws
  refine ⟨K, ?_⟩
  intro A C u v hu hv σ hleft hright
  exact hK A C (by simp [pairs]) u
    (by simpa [ws] using (List.mem_sublists).2 hu) v
    (by simpa [ws] using (List.mem_sublists).2 hv) σ hleft hright

/-- First-step normal-form decomposition with the binary case shrunk to one bounded common
inherited stack. In the binary branch, the returned stack `τ` still generates both children,
is a sublist of the original inherited stack, is bounded uniformly for the target word, and
reconstructs a parent derivation from `[A τ]`.

This is the bridge from the rule-level decomposition in `Bounds.lean` to the stack-shrinking
argument: binary composition is preserved because both children use the same shrunken stack. -/
theorem exists_bound_rule_binary_common_substack_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (target : List T) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
        w <+ target →
        g.Derives [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u <+ target ∧ v <+ target ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          g.Derives [ISym.indexed B τ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C τ]
            (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed A τ]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B ρ]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C ρ]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ) ∨
        (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
          ∃ r ∈ g.rules,
            σ = f :: ρ ∧
            r.lhs = A ∧ r.consume = some f ∧
            r.rhs = [IRhsSymbol.nonterminal B none] ∧
            g.Derives [ISym.indexed B ρ]
              (w.map fun a => (ISym.terminal a : g.ISym))) ∨
        (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
          g.Derives [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
        (∃ a : T, ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
            w = [a]) := by
  obtain ⟨K, hK⟩ := exists_bound_generating_pair_substack_for_target_sublists
    (g := g) target
  refine ⟨K, ?_⟩
  intro A σ w hwt hder
  have hcases :=
    derives_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (A := A) (σ := σ) (w := w) (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
      hK B C u v husub hvsub σ hleft hright
    have hparent :
        g.Derives [ISym.indexed A τ]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := τ) (w := w)).mpr
      left
      exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hτleft, hτright⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen,
      hτleft, hτright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · right
    right
    left
    exact hpush
  · right
    right
    right
    exact hterm

/-- First-step normal-form decomposition with both structural stack-copying branches shrunk:
binary branches get one bounded common inherited stack, and push branches get a bounded base
substack below the freshly pushed flag. Both shrunk branches reconstruct the corresponding
parent derivation from the shrunk stack. -/
theorem exists_bound_rule_binary_push_substack_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (target : List T) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
        w <+ target →
        g.Derives [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u <+ target ∧ v <+ target ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          g.Derives [ISym.indexed B τ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C τ]
            (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed A τ]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B ρ]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C ρ]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ) ∨
        (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
          ∃ r ∈ g.rules,
            σ = f :: ρ ∧
            r.lhs = A ∧ r.consume = some f ∧
            r.rhs = [IRhsSymbol.nonterminal B none] ∧
            g.Derives [ISym.indexed B ρ]
              (w.map fun a => (ISym.terminal a : g.ISym))) ∨
        (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          g.Derives [ISym.indexed B (f :: τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed A τ]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B (f :: ρ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ) ∨
        (∃ a : T, ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
            w = [a]) := by
  obtain ⟨Kbin, hKbin⟩ := exists_bound_generating_pair_substack_for_target_sublists
    (g := g) target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_generating_pushed_substack_for_target_sublists (g := g) target
  refine ⟨max Kbin Kpush, ?_⟩
  intro A σ w hwt hder
  have hcases :=
    derives_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (A := A) (σ := σ) (w := w) (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
      hKbin B C u v husub hvsub σ hleft hright
    have hparent :
        g.Derives [ISym.indexed A τ]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := τ) (w := w)).mpr
      left
      exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hτleft, hτright⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush),
      hτleft, hτright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hchild⟩
    obtain ⟨τ, hτchild, hτsub, hτlen, hτmin⟩ :=
      hKpush B f w hwt σ hchild
    have hparent :
        g.Derives [ISym.indexed A τ]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, hτchild⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub,
      le_trans hτlen (Nat.le_max_right Kbin Kpush), hτchild, hparent, hτmin⟩
  · right
    right
    right
    exact hterm

theorem exists_bound_generating_cons_prefixed_suffix_for_flag_list
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (flags : List g.flag) (pref : List g.flag) (target : List T) :
    ∃ K : ℕ,
      ∀ f ∈ flags,
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A ((f :: pref) ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A ((f :: pref) ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction flags with
  | nil =>
      exact ⟨0, by simp⟩
  | cons f flags ih =>
      obtain ⟨Kf, hKf⟩ :=
        exists_bound_generating_prefixed_suffix_for_target_sublists
          (g := g) (pref := f :: pref) target
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kf Ktail, ?_⟩
      intro f' hf' A w hw σ hder
      rcases List.mem_cons.mp hf' with rfl | hf_tail
      · obtain ⟨τ, hτ, hτsub, hτlen, hτmin⟩ := hKf A w hw σ hder
        exact ⟨τ, hτ, hτsub, le_trans hτlen (Nat.le_max_left Kf Ktail), hτmin⟩
      · obtain ⟨τ, hτ, hτsub, hτlen, hτmin⟩ :=
          hKtail f' hf_tail A w hw σ hder
        exact ⟨τ, hτ, hτsub, le_trans hτlen (Nat.le_max_right Kf Ktail), hτmin⟩

theorem exists_bound_generating_cons_prefixed_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (pref : List g.flag) (target : List T) :
    ∃ K : ℕ,
      ∀ f : g.flag, ∀ A : g.nt, ∀ w : List T,
        w <+ target →
        ∀ σ : List g.flag,
          g.Derives [ISym.indexed A ((f :: pref) ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ τ : List g.flag,
            g.Derives [ISym.indexed A ((f :: pref) ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed A ((f :: pref) ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  let flags : List g.flag := (Finset.univ : Finset g.flag).toList
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_cons_prefixed_suffix_for_flag_list
      (g := g) flags pref target
  refine ⟨K, ?_⟩
  intro f A w hw σ hder
  exact hK f (by simp [flags]) A w hw σ hder

theorem exists_bound_generating_prefixed_suffix_for_prefix_list_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (prefixes : List (List g.flag)) (target : List T) :
    ∃ K : ℕ,
      ∀ pref ∈ prefixes,
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction prefixes with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pref prefixes ih =>
      obtain ⟨Kpref, hKpref⟩ :=
        exists_bound_generating_prefixed_suffix_for_target_sublists
          (g := g) pref target
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpref Ktail, ?_⟩
      intro pref' hpref' A w hw σ hder
      rcases List.mem_cons.mp hpref' with rfl | hpref_tail
      · obtain ⟨τ, hτ, hτsub, hτlen, hτmin⟩ := hKpref A w hw σ hder
        exact ⟨τ, hτ, hτsub, le_trans hτlen (Nat.le_max_left Kpref Ktail), hτmin⟩
      · obtain ⟨τ, hτ, hτsub, hτlen, hτmin⟩ :=
          hKtail pref' hpref_tail A w hw σ hder
        exact ⟨τ, hτ, hτsub, le_trans hτlen (Nat.le_max_right Kpref Ktail), hτmin⟩

theorem exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  have hprefixes :
      ({pref : List g.flag | pref.length ≤ N} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag N
  let prefixes : List (List g.flag) := (Set.Finite.toFinset hprefixes).toList
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_prefix_list_target_sublists
      (g := g) prefixes target
  refine ⟨K, ?_⟩
  intro pref hpref A w hw σ hder
  have hprefFinset : pref ∈ Set.Finite.toFinset hprefixes := by
    rw [Set.Finite.mem_toFinset]
    exact hpref
  have hprefList : pref ∈ prefixes := by
    simpa [prefixes] using hprefFinset
  exact hK pref hprefList A w hw σ hder

/-- Length-uniform unbudgeted bounded-prefix suffix shrinking. For a finite terminal alphabet,
one suffix bound works for every target word of length at most `L`, every sublist yield of
that target, and every live prefix of length at most `N`. -/
theorem exists_bound_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A : g.nt, ∀ w : List T,
            w <+ target →
            ∀ σ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ∃ τ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                τ <+ σ ∧
                τ.length ≤ K ∧
                ∀ ρ : List g.flag,
                  g.Derives [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
        (g := g) N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref A w hwt σ hder
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
        (g := g) N target)
  obtain ⟨τ, hτder, hτsub, hτlen, hτmin⟩ :=
    htarget pref hpref A w hwt σ hder
  exact ⟨τ, hτder, hτsub, le_trans hτlen hle, hτmin⟩

/-- Length-uniform bound for suffixes that are already sublist-minimal under an uncounted
prefixed derivability predicate. -/
theorem exists_bound_minimal_generating_prefixed_suffix_length_for_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.Derives [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ ρ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ σ → ρ = σ) →
            σ.length ≤ K := by
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hder hmin
  obtain ⟨τ, hτder, hτsub, hτlen, _hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt σ hder
  have hτσ : τ = σ := hmin τ hτder hτsub
  simpa [← hτσ] using hτlen

/-- Counted version of
`exists_bound_minimal_generating_prefixed_suffix_length_for_target_length_bounded_prefix`.
The bounded sub-suffix is obtained by uncounted shrinking and then converted back to a counted
derivation before applying the counted minimality hypothesis. -/
theorem exists_bound_counted_minimal_generating_prefixed_suffix_length_for_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ ρ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ σ → ρ = σ) →
            σ.length ≤ K := by
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin
  obtain ⟨τ, hτder, hτsub, hτlen, _hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt σ (derives_of_derivesIn (g := g) hder)
  obtain ⟨m, hτderIn⟩ := exists_derivesIn_of_derives (g := g) hτder
  have hτσ : τ = σ := hmin τ m hτderIn hτsub
  simpa [← hτσ] using hτlen

/-- Length-uniform counted bounded-prefix suffix shrinking without a step budget. Every
counted derivation below a live prefix of length at most `N`, to a sublist of a target of
length at most `L`, has a bounded sub-suffix with some counted derivation to the same yield. -/
theorem exists_bound_counted_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ m : ℕ, ∃ τ : List g.flag,
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder
  obtain ⟨τ, hτder, hτsub, hτlen, hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt σ (derives_of_derivesIn (g := g) hder)
  obtain ⟨m, hτderIn⟩ := exists_derivesIn_of_derives (g := g) hτder
  refine ⟨m, τ, hτsub, hτlen, hτderIn, ?_⟩
  intro ρ k hρder hρsub
  exact hτmin ρ (derives_of_derivesIn (g := g) hρder) hρsub

/-- Trace-local form of the length-uniform counted suffix shrinker. For every indexed symbol
that occurs in an accepting trace of a word of length at most `L`, once its stack is split as
`pref ++ σ` with `pref.length ≤ N`, the symbol's own future terminal yield has a bounded
sub-suffix `τ <+ σ` that still generates that yield. -/
theorem exists_bound_accepting_derivationTrace_indexed_mem_local_suffix_shrink
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              pref.length ≤ N →
              ISym.indexed A (pref ++ σ) ∈ trace.get ⟨i, hi⟩ →
              ∃ m : ℕ, ∃ τ : List g.flag, ∃ w : List T,
                w <+ target ∧ w.length ≤ L ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ ρ : List g.flag, ∀ k : ℕ,
                  g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi A pref σ hpref hmem
  obtain ⟨n, w, hwt, hwlen, hlocal⟩ :=
    accepting_derivationTrace_indexed_mem_exists_local_derivesIn
      (g := g) htrace hlast htargetLen hi hmem
  obtain ⟨m, τ, hτsub, hτlen, hτder, hτmin⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hlocal
  exact ⟨m, τ, w, hwt, hwlen, hτsub, hτlen, hτder, hτmin⟩

/-- Context replacement form of the trace-local shrinker. If a trace suffix starts from an
explicit context `u ++ [A[pref ++ σ]] ++ v`, then the suffix generated by the distinguished
symbol can be shrunk to a bounded `τ <+ σ`, and the whole modified context
`u ++ [A[pref ++ τ]] ++ v` still derives the original accepted target. -/
theorem exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              pref.length ≤ N →
              ∀ u v : List g.ISym,
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                ∃ m : ℕ, ∃ τ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                  w <+ target ∧ w.length ≤ L ∧
                  τ <+ σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  ∀ ρ : List g.flag, ∀ k : ℕ,
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi A pref σ hpref u v hctx
  obtain ⟨nu, ns, nv, wu, w, wv, _hsum, hw, hwt, hu, hlocal, hv⟩ :=
    accepting_derivationTrace_indexed_context_suffix_to_terminals_split
      (g := g) htrace hlast hi hctx
  obtain ⟨m, τ, hτsub, hτlen, hτder, hτmin⟩ :=
    hK target htargetLen pref hpref ns A σ w hwt hlocal
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  have hreplacement :
      g.DerivesIn (nu + m + nv) (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    have hcomp :=
      derivesIn_context_indexed_to_terminals_of_derivesIn
        (g := g) (u := u) (v := v) (A := A) (σ := pref ++ τ)
        (nu := nu) (ns := m) (nv := nv)
        (wu := wu) (ws := w) (wv := wv) hu hτder hv
    simpa [hw] using hcomp
  exact ⟨m, τ, w, nu + m + nv, hwt, hwlen, hτsub, hτlen, hτder,
    hreplacement, hτmin⟩

/-- Max-stack occurrence form of the trace-local shrinker. At any trace position with positive
maximum stack height, choose an indexed symbol attaining that maximum, split its stack after
the first `N` flags, and shrink the remaining suffix for that symbol's own future yield. -/
theorem exists_bound_accepting_derivationTrace_max_stack_local_suffix_shrink
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
            ∃ A : g.nt, ∃ η pref σ τ : List g.flag, ∃ m : ℕ, ∃ w : List T,
              ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
              η = pref ++ σ ∧
              pref.length ≤ N ∧
              η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
              w <+ target ∧ w.length ≤ L ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_mem_local_suffix_shrink
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hpos
  obtain ⟨A, η, hmem, hηmax⟩ :=
    exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
      (g := g) (w := trace.get ⟨i, hi⟩) hpos
  let pref : List g.flag := η.take N
  let σ : List g.flag := η.drop N
  have hη : η = pref ++ σ := by
    unfold pref σ
    exact (List.take_append_drop N η).symm
  have hpref : pref.length ≤ N := by
    unfold pref
    exact List.length_take_le N η
  have hmem' : ISym.indexed A (pref ++ σ) ∈ trace.get ⟨i, hi⟩ := by
    simpa [← hη] using hmem
  obtain ⟨m, τ, w, hwt, hwlen, hτsub, hτlen, hτder, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hpref hmem'
  exact ⟨A, η, pref, σ, τ, m, w, hmem, hη, hpref, hηmax, hwt, hwlen,
    hτsub, hτlen, hτder, hτmin⟩

/-- If the maximum stack height at a trace position is above `B`, the max-stack local shrinker
chooses a witnessing indexed symbol whose original stack is also above `B`. -/
theorem exists_bound_accepting_derivationTrace_high_stack_local_suffix_shrink
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length, ∀ B : ℕ,
            B < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
            ∃ A : g.nt, ∃ η pref σ τ : List g.flag, ∃ m : ℕ, ∃ w : List T,
              ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
              B < η.length ∧
              η = pref ++ σ ∧
              pref.length ≤ N ∧
              η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
              w <+ target ∧ w.length ≤ L ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_max_stack_local_suffix_shrink
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi B hgt
  have hpos : 0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) := by omega
  obtain ⟨A, η, pref, σ, τ, m, w, hmem, hη, hpref, hηmax, hwt, hwlen,
      hτsub, hτlen, hτder, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi hpos
  exact ⟨A, η, pref, σ, τ, m, w, hmem, by omega, hη, hpref, hηmax, hwt,
    hwlen, hτsub, hτlen, hτder, hτmin⟩

/-- Counted version of bounded-prefix suffix shrinking. Every counted derivation below a live
prefix of length at most `N` has a sub-suffix of uniformly bounded length that still has some
counted derivation to the same terminal yield, and the chosen sub-suffix is sublist-minimal
among all counted derivations preserving that prefix and yield. -/
theorem exists_bound_counted_generating_prefixed_suffix_for_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ∃ m : ℕ, ∃ τ : List g.flag,
            τ <+ σ ∧ τ.length ≤ K ∧
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            ∀ ρ : List g.flag, ∀ k : ℕ,
              g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
      (g := g) N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder
  obtain ⟨τ, hτder, hτsub, hτlen, hτmin⟩ :=
    hK pref hpref A w hwt σ (derives_of_derivesIn (g := g) hder)
  obtain ⟨m, hm⟩ := exists_derivesIn_of_derives (g := g) hτder
  refine ⟨m, τ, hτsub, hτlen, hm, ?_⟩
  intro ρ k hρder hρsub
  exact hτmin ρ (derives_of_derivesIn (g := g) hρder) hρsub

theorem exists_bound_generating_prefixed_pair_suffix_for_prefix_list_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (prefixes : List (List g.flag)) (target : List T) :
    ∃ K : ℕ,
      ∀ pref ∈ prefixes,
        ∀ A C : g.nt, ∀ u v : List T,
          u <+ target →
          v <+ target →
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.Derives [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  induction prefixes with
  | nil =>
      exact ⟨0, by simp⟩
  | cons pref prefixes ih =>
      obtain ⟨Kpref, hKpref⟩ :=
        exists_bound_generating_prefixed_pair_suffix_for_target_sublists
          (g := g) pref target
      obtain ⟨Ktail, hKtail⟩ := ih
      refine ⟨max Kpref Ktail, ?_⟩
      intro pref' hpref' A C u v hu hv σ hleft hright
      rcases List.mem_cons.mp hpref' with rfl | hpref_tail
      · obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKpref A C u v hu hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_left Kpref Ktail), hτmin⟩
      · obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
          hKtail pref' hpref_tail A C u v hu hv σ hleft hright
        exact ⟨τ, hτleft, hτright, hτsub,
          le_trans hτlen (Nat.le_max_right Kpref Ktail), hτmin⟩

theorem exists_bound_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag]
    (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ A C : g.nt, ∀ u v : List T,
          u <+ target →
          v <+ target →
          ∀ σ : List g.flag,
            g.Derives [ISym.indexed A (pref ++ σ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C (pref ++ σ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ τ : List g.flag,
              g.Derives [ISym.indexed A (pref ++ τ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C (pref ++ τ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed A (pref ++ ρ)]
                    (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.Derives [ISym.indexed C (pref ++ ρ)]
                    (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  have hprefixes :
      ({pref : List g.flag | pref.length ≤ N} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag N
  let prefixes : List (List g.flag) := (Set.Finite.toFinset hprefixes).toList
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_pair_suffix_for_prefix_list_target_sublists
      (g := g) prefixes target
  refine ⟨K, ?_⟩
  intro pref hpref A C u v hu hv σ hleft hright
  have hprefFinset : pref ∈ Set.Finite.toFinset hprefixes := by
    rw [Set.Finite.mem_toFinset]
    exact hpref
  have hprefList : pref ∈ prefixes := by
    simpa [prefixes] using hprefFinset
  exact hK pref hprefList A C u v hu hv σ hleft hright

/-- Fixed-prefix first-step shrinking for normal-form derivations. Binary branches shrink the
common inherited suffix while preserving `pref`; push branches shrink the suffix below the
fresh top flag and the existing prefix, preserving `(f :: pref)`. In both shrinking branches
the parent derivation is reconstructed from the shrunken stack. -/
theorem exists_bound_rule_binary_push_prefixed_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (pref : List g.flag) (target : List T) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
        w <+ target →
        g.Derives [ISym.indexed A (pref ++ σ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u <+ target ∧ v <+ target ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          g.Derives [ISym.indexed B (pref ++ τ)]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C (pref ++ τ)]
            (v.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed A (pref ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B (pref ++ ρ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) →
            g.Derives [ISym.indexed C (pref ++ ρ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ) ∨
        (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
          ∃ r ∈ g.rules,
            pref ++ σ = f :: ρ ∧
            r.lhs = A ∧ r.consume = some f ∧
            r.rhs = [IRhsSymbol.nonterminal B none] ∧
            g.Derives [ISym.indexed B ρ]
              (w.map fun a => (ISym.terminal a : g.ISym))) ∨
        (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          g.Derives [ISym.indexed B ((f :: pref) ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed A (pref ++ τ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ ρ : List g.flag,
            g.Derives [ISym.indexed B ((f :: pref) ++ ρ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ρ <+ τ → ρ = τ) ∨
        (∃ a : T, ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
            w = [a]) := by
  obtain ⟨Kbin, hKbin⟩ :=
    exists_bound_generating_prefixed_pair_suffix_for_target_sublists
      (g := g) pref target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_generating_cons_prefixed_suffix_for_target_sublists
      (g := g) pref target
  refine ⟨max Kbin Kpush, ?_⟩
  intro A σ w hwt hder
  have hcases :=
    derives_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (A := A) (σ := pref ++ σ) (w := w) (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
      hKbin B C u v husub hvsub σ hleft hright
    have hparent :
        g.Derives [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := pref ++ τ) (w := w)).mpr
      left
      exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hτleft, hτright⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush),
      hτleft, hτright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hchild⟩
    obtain ⟨τ, hτchild, hτsub, hτlen, hτmin⟩ :=
      hKpush f B w hwt σ (by simpa using hchild)
    have hparent :
        g.Derives [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := pref ++ τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, by simpa using hτchild⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub,
      le_trans hτlen (Nat.le_max_right Kbin Kpush), hτchild, hparent, hτmin⟩
  · right
    right
    right
    exact hterm

/-- Uniform bounded-prefix version of
`exists_bound_rule_binary_push_prefixed_suffix_for_target_sublists`. For every live prefix
of length at most `N`, binary branches shrink the common inherited suffix under that prefix,
and push branches shrink below the extended prefix `(f :: pref)`. -/
theorem exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.Derives [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
            w = u ++ v ∧
            0 < u.length ∧ 0 < v.length ∧
            u.length < w.length ∧ v.length < w.length ∧
            u <+ target ∧ v <+ target ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            g.Derives [ISym.indexed B (pref ++ τ)]
              (u.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed C (pref ++ τ)]
              (v.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed B (pref ++ ρ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) →
              g.Derives [ISym.indexed C (pref ++ ρ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              g.Derives [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            g.Derives [ISym.indexed B ((f :: pref) ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.Derives [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            ∀ ρ : List g.flag,
              g.Derives [ISym.indexed B ((f :: pref) ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a]) := by
  obtain ⟨Kbin, hKbin⟩ :=
    exists_bound_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
      (g := g) N target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
      (g := g) (N + 1) target
  refine ⟨max Kbin Kpush, ?_⟩
  intro pref hpref A σ w hwt hder
  have hcases :=
    derives_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (A := A) (σ := pref ++ σ) (w := w) (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
      hKbin pref hpref B C u v husub hvsub σ hleft hright
    have hparent :
        g.Derives [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := pref ++ τ) (w := w)).mpr
      left
      exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hτleft, hτright⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush),
      hτleft, hτright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hchild⟩
    have hfpref : (f :: pref).length ≤ N + 1 := by
      simp
      omega
    obtain ⟨τ, hτchild, hτsub, hτlen, hτmin⟩ :=
      hKpush (f :: pref) hfpref B w hwt σ (by simpa using hchild)
    have hparent :
        g.Derives [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derives_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := pref ++ τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, by simpa using hτchild⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub,
      le_trans hτlen (Nat.le_max_right Kbin Kpush), hτchild, hparent, hτmin⟩
  · right
    right
    right
    exact hterm

/-- Length-uniform version of
`exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_sublists`. One first-step
shrinking bound works for every target word of length at most `L`. -/
theorem exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_length_sublists
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.Derives [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.Derives [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed B (pref ++ ρ)]
                  (u.map fun a => (ISym.terminal a : g.ISym)) →
                g.Derives [ISym.indexed C (pref ++ ρ)]
                  (v.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ) ∨
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref ++ σ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                g.Derives [ISym.indexed B ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym))) ∨
            (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.Derives [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag,
                g.Derives [ISym.indexed B ((f :: pref) ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ) ∨
            (∃ a : T, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
                w = [a]) := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_sublists
        (g := g) hNF N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hder
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_sublists
        (g := g) hNF N target)
  rcases htarget pref hpref A σ w hwt hder with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen,
        hleft, hright, hparent, hτmin⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen hle, hleft, hright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · rcases hpush with
      ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, hτlen, hchild, hparent, hτmin⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub,
      le_trans hτlen hle, hchild, hparent, hτmin⟩
  · right
    right
    right
    exact hterm

theorem append_eq_cons_cases {α : Type} {pref σ : List α} {f : α} {ρ : List α}
    (h : pref ++ σ = f :: ρ) :
    (pref = [] ∧ σ = f :: ρ) ∨
      ∃ pref' : List α, pref = f :: pref' ∧ ρ = pref' ++ σ := by
  cases pref with
  | nil =>
      left
      simpa using h
  | cons x pref' =>
      right
      simp at h
      rcases h with ⟨rfl, htail⟩
      exact ⟨pref', rfl, htail.symm⟩

theorem pop_prefix_suffix_budget_cases {g : IndexedGrammar T}
    {N n : ℕ} {pref σ : List g.flag} {f : g.flag} {ρ : List g.flag}
    (hbudget : pref.length + (n + 1) ≤ N)
    (hstack : pref ++ σ = f :: ρ) :
    (pref = [] ∧ σ = f :: ρ ∧ n ≤ N) ∨
      ∃ pref' : List g.flag,
        pref = f :: pref' ∧ ρ = pref' ++ σ ∧ pref'.length + n ≤ N := by
  rcases append_eq_cons_cases (pref := pref) (σ := σ) (f := f) (ρ := ρ) hstack with
    hempty | hcons
  · rcases hempty with ⟨hpref, hσ⟩
    left
    refine ⟨hpref, hσ, ?_⟩
    omega
  · rcases hcons with ⟨pref', hpref, hρ⟩
    right
    refine ⟨pref', hpref, hρ, ?_⟩
    subst pref
    simp at hbudget ⊢
    omega

/-- Counted bounded-prefix first-step shrinking. This is the recursion-facing form of the
bounded-prefix shrinking theorem: after a counted first-step decomposition, the binary and
push branches are shrunk and then converted back to counted derivations from the shrunken
stacks. The new counts need not match the original sub-budgets; they are the counts of the
new shrunken derivations. -/
theorem exists_bound_counted_rule_binary_push_bounded_prefix_suffix_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
            ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn k [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n < n + 1 ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ m : ℕ, ∃ r ∈ g.rules,
            ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              n < n + 1 ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨Kbin, hKbin⟩ :=
    exists_bound_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
      (g := g) N target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_generating_prefixed_suffix_for_bounded_prefix_target_sublists
      (g := g) (N + 1) target
  refine ⟨max Kbin Kpush, ?_⟩
  intro pref hpref n A σ w hwt hder
  have hcases :=
    derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := pref ++ σ) (w := w)
      (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m₀, k₀, u, v, r, hr, hlhs, hc, hrhs, _hmk, _hm_lt, _hk_lt, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    obtain ⟨τ, hτleft, hτright, hτsub, hτlen, _hτmin⟩ :=
      hKbin pref hpref B C u v husub hvsub σ
        (derives_of_derivesIn (g := g) hleft)
        (derives_of_derivesIn (g := g) hright)
    obtain ⟨m, hm⟩ := exists_derivesIn_of_derives (g := g) hτleft
    obtain ⟨k, hk⟩ := exists_derivesIn_of_derives (g := g) hτright
    left
    exact ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush), hm, hk⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hn, hrest⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hn, hrest⟩
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hn, hchild⟩
    have hfpref : (f :: pref).length ≤ N + 1 := by
      simp
      omega
    obtain ⟨τ, hτchild, hτsub, hτlen, _hτmin⟩ :=
      hKpush (f :: pref) hfpref B w hwt σ
        (by
          have hchildD := derives_of_derivesIn (g := g) hchild
          simpa using hchildD)
    obtain ⟨m, hm⟩ := exists_derivesIn_of_derives (g := g) hτchild
    right
    right
    left
    exact ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hn, hτsub,
      le_trans hτlen (Nat.le_max_right Kbin Kpush), hm⟩
  · right
    right
    right
    exact hterm

/-- Counted bounded-prefix first-step shrinking, with the shrunken binary and push parent
derivations reconstructed. This is the form needed by recursive bounded-stack construction:
after shrinking the inherited suffix, the parent nonterminal at the shrunken stack still has a
counted derivation to the same terminal yield. -/
theorem exists_bound_counted_rule_binary_push_bounded_prefix_suffix_with_parent_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
            ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn k [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n < n + 1 ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ m : ℕ, ∃ r ∈ g.rules,
            ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              n < n + 1 ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_rule_binary_push_bounded_prefix_suffix_for_target_sublists
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder
  have hcases := hK pref hpref n A σ w hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen, hleft, hright⟩
    have hparent0 :
        g.DerivesIn ((m + k) + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m + k) (A := A) (σ := pref ++ τ) (w := w)).mpr
      left
      exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, rfl, hw, hleft, hright⟩
    have hparent :
        g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    left
    exact ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen, hleft, hright, hparent⟩
  · right
    left
    exact hpop
  · rcases hpush with
      ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hn, hτsub, hτlen, hchild⟩
    have hparent0 :
        g.DerivesIn (m + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m) (A := A) (σ := pref ++ τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, hchild⟩
    have hparent :
        g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    right
    right
    left
    exact ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hn, hτsub, hτlen, hchild, hparent⟩
  · right
    right
    right
    exact hterm

/-- Budget-preserving counted bounded-prefix first-step shrinking. Unlike
`exists_bound_counted_rule_binary_push_bounded_prefix_suffix_with_parent_for_target_sublists`,
the binary and push branches keep explicit child derivation counts below the supplied global
budget `N`; the reconstructed parent derivation is returned with the count induced by the
shrunken children. -/
theorem exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_with_parent_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
            ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              m ≤ N ∧ k ≤ N ∧
              g.DerivesIn m [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn k [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ m : ℕ, ∃ r ∈ g.rules,
            ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              m ≤ N ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨Kbin, hKbin⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
      (g := g) P N N target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_bounded_prefix_target_sublists
      (g := g) (P + 1) N target
  refine ⟨max Kbin Kpush, ?_⟩
  intro pref hpref n A σ w hnN hwt hder
  have hcases :=
    derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := pref ++ σ) (w := w)
      (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m₀, k₀, u, v, r, hr, hlhs, hc, hrhs, hmk, _hm_lt, _hk_lt, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    have hm₀N : m₀ ≤ N := by omega
    have hk₀N : k₀ ≤ N := by omega
    obtain ⟨τ, m, k, hmN, hkN, hτleft, hτright, hτsub, hτlen, _hτmin⟩ :=
      hKbin pref hpref B C u v husub hvsub σ
        ⟨m₀, hm₀N, hleft⟩ ⟨k₀, hk₀N, hright⟩
    have hparent0 :
        g.DerivesIn ((m + k) + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m + k) (A := A) (σ := pref ++ τ) (w := w)).mpr
      left
      exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, rfl, hw, hτleft, hτright⟩
    have hparent :
        g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    left
    exact ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush), hmN, hkN,
      hτleft, hτright, hparent⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, _hn, hrest⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, by omega, hrest⟩
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, _hn, hchild⟩
    have hfpref : (f :: pref).length ≤ P + 1 := by
      simp
      omega
    have hn_child : n ≤ N := by omega
    obtain ⟨τ, m, hmN, hτchild, hτsub, hτlen, _hτmin⟩ :=
      hKpush (f :: pref) hfpref B w hwt σ
        ⟨n, hn_child, by simpa using hchild⟩
    have hparent0 :
        g.DerivesIn (m + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m) (A := A) (σ := pref ++ τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, by simpa using hτchild⟩
    have hparent :
        g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    right
    right
    left
    exact ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hmN, hτsub,
      le_trans hτlen (Nat.le_max_right Kbin Kpush), hτchild, hparent⟩
  · right
    right
    right
    exact hterm

/-- Budget-preserving counted first-step shrinking with the reconstructed parent count still
below the original global budget. Binary branches are shrunk using their original child
budgets, so the new child counts still add to at most the original tail budget `n`; push
branches similarly keep the child count at most `n`. -/
theorem exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_preserves_parent_budget_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
            ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              m + k ≤ n ∧ 1 + (m + k) ≤ N ∧
              g.DerivesIn m [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn k [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ m : ℕ, ∃ r ∈ g.rules,
            ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              m ≤ n ∧ 1 + m ≤ N ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨Kbin, hKbin⟩ :=
    exists_bound_budgeted_generating_prefixed_pair_suffix_for_budget_upto_bounded_prefix_target_sublists
      (g := g) P N target
  obtain ⟨Kpush, hKpush⟩ :=
    exists_bound_budgeted_generating_prefixed_suffix_for_budget_upto_bounded_prefix_target_sublists
      (g := g) (P + 1) N target
  refine ⟨max Kbin Kpush, ?_⟩
  intro pref hpref n A σ w hnN hwt hder
  have hcases :=
    derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := pref ++ σ) (w := w)
      (target := target) hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m₀, k₀, u, v, r, hr, hlhs, hc, hrhs, hmk, _hm_lt, _hk_lt, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hleft, hright⟩
    have hn_le_N : n ≤ N := by omega
    have hm₀N : m₀ ≤ N := by omega
    have hk₀N : k₀ ≤ N := by omega
    obtain ⟨τ, m, k, hm_m₀, hk_k₀, hτleft, hτright, hτsub, hτlen, _hτmin⟩ :=
      hKbin m₀ k₀ hm₀N hk₀N pref hpref B C u v husub hvsub σ
        ⟨m₀, le_rfl, hleft⟩ ⟨k₀, le_rfl, hright⟩
    have hmk_le : m + k ≤ n := by omega
    have hparent0 :
        g.DerivesIn ((m + k) + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m + k) (A := A) (σ := pref ++ τ) (w := w)).mpr
      left
      exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, rfl, hw, hτleft, hτright⟩
    have hparent :
        g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    left
    exact ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub,
      le_trans hτlen (Nat.le_max_left Kbin Kpush),
      hmk_le, by omega, hτleft, hτright, hparent⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, _hn, hrest⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, by omega, hrest⟩
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, _hn, hchild⟩
    have hfpref : (f :: pref).length ≤ P + 1 := by
      simp
      omega
    have hn_le_N : n ≤ N := by omega
    obtain ⟨τ, m, hm_n, hτchild, hτsub, hτlen, _hτmin⟩ :=
      hKpush n hn_le_N (f :: pref) hfpref B w hwt σ
        ⟨n, le_rfl, by simpa using hchild⟩
    have hparent0 :
        g.DerivesIn (m + 1) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := m) (A := A) (σ := pref ++ τ) (w := w)).mpr
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, by simpa using hτchild⟩
    have hparent :
        g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [Nat.add_comm] using hparent0
    right
    right
    left
    exact ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hm_n, by omega,
      hτsub, le_trans hτlen (Nat.le_max_right Kbin Kpush), hτchild, hparent⟩
  · right
    right
    right
    exact hterm

/-- Combined-budget form of the budget-preserving first-step shrinker. Besides preserving the
local child budgets, the binary and push branches expose the arithmetic needed to recurse
under the same bound on `live prefix length + remaining derivation length`. -/
theorem exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_preserves_combined_budget_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (Q : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          pref.length + (n + 1) ≤ Q →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
            ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              m + k ≤ n ∧
              pref.length + m ≤ Q ∧
              pref.length + k ≤ Q ∧
              pref.length + (1 + (m + k)) ≤ Q ∧
              g.DerivesIn m [ISym.indexed B (pref ++ τ)]
                (u.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn k [ISym.indexed C (pref ++ τ)]
                (v.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + (m + k)) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ Q ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ m : ℕ, ∃ r ∈ g.rules,
            ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              m ≤ n ∧
              (f :: pref).length + m ≤ Q ∧
              pref.length + (1 + m) ≤ Q ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed B ((f :: pref) ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.DerivesIn (1 + m) [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_preserves_parent_budget_for_target_sublists
      (g := g) hNF Q Q target
  refine ⟨K, ?_⟩
  intro pref n A σ w hbudget hwt hder
  have hpref : pref.length ≤ Q := by omega
  have hnQ : n + 1 ≤ Q := by omega
  have hcases := hK pref hpref n A σ w hnQ hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen,
        hmk_le, _hparentBudget, hleft, hright, hparent⟩
    left
    exact ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen, hmk_le,
      by omega, by omega, by omega, hleft, hright, hparent⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, _hnQ, hchild⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, by omega, hchild⟩
  · rcases hpush with
      ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hm_le, _hparentBudget,
        hτsub, hτlen, hchild, hparent⟩
    right
    right
    left
    exact ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hm_le,
      by simp; omega, by omega, hτsub, hτlen, hchild, hparent⟩
  · right
    right
    right
    exact hterm

/-- Budget-minimal forced-pop lemma. If the visible suffix is sublist-minimal among all
derivations of the same yield using at most `N` steps, then a long suffix cannot start with a
binary, push, or terminal step: the budget-preserving shrinker would produce a shorter
budgeted parent derivation. -/
theorem exists_bound_budgeted_first_step_pop_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ N →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          ∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_preserves_parent_budget_for_target_sublists
      (g := g) hNF P N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hnN hwt hder hmin hlong
  have hcases := hK pref hpref n A σ w hnN hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen,
        _hmk_le, hparentBudget, hleft, hright, hparent⟩
    have hτσ : τ = σ :=
      hmin τ (1 + (m + k)) hparentBudget hparent hτsub
    subst τ
    omega
  · exact hpop
  · rcases hpush with
      ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, _hmn, hparentBudget,
        hτsub, hτlen, hchild, hparent⟩
    have hτσ : τ = σ :=
      hmin τ (1 + m) hparentBudget hparent hτsub
    subst τ
    omega
  · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
    subst w
    subst n
    have hempty :
        g.DerivesIn 1 [ISym.indexed A (pref ++ [])]
          ([a].map fun b => (ISym.terminal b : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := 0) (A := A) (σ := pref ++ []) (w := [a])).mpr
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, rfl, rfl⟩
    have hempty_eq : ([] : List g.flag) = σ := by
      exact hmin [] 1 (by omega) (by simpa using hempty) (List.nil_sublist σ)
    have hσlen : σ.length = 0 := by
      simp [← hempty_eq]
    omega

/-- Prefix/suffix split for
`exists_bound_budgeted_first_step_pop_of_suffix_minimal_long`. The forced pop either consumes
the visible suffix head, or consumes one symbol from the live prefix and leaves the suffix under
a strictly shorter prefix. -/
theorem exists_bound_budgeted_first_step_pop_cases_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ N →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = [] ∧ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = f :: pref' ∧ pref'.length < pref.length ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_first_step_pop_of_suffix_minimal_long
      (g := g) hNF P N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hnN hwt hder hmin hlong
  obtain ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, hnBudget, hchild⟩ :=
    hK pref hpref n A σ w hnN hwt hder hmin hlong
  rcases append_eq_cons_cases (pref := pref) (σ := σ) (f := f) (ρ := ρ) hstack with
    hempty | hcons
  · rcases hempty with ⟨hpref, hσ⟩
    left
    exact ⟨f, ρ, B, r, hr, hpref, hσ, hlhs, hc, hrhs, hnBudget, hchild⟩
  · rcases hcons with ⟨pref', hpref, hρ⟩
    right
    subst pref
    subst ρ
    exact ⟨f, pref', B, r, hr, rfl, by simp, hlhs, hc, hrhs, hnBudget, hchild⟩

/-- Local-budget forced-pop lemma. The minimality budget is the current parent derivation
length rather than a fixed global cap, which is the invariant needed when recursing into the
child of a pop rule. -/
theorem exists_bound_locally_budgeted_first_step_pop_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ n + 1 →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          ∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_budgeted_counted_rule_binary_push_bounded_prefix_suffix_preserves_parent_budget_for_target_sublists
      (g := g) hNF P N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hnN hwt hder hmin hlong
  have hcases := hK pref hpref n A σ w hnN hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, τ, hlhs, hc, hrhs, hw,
        hupos, hvpos, hult, hvlt, husub, hvsub, hτsub, hτlen,
        hmk_le, _hparentBudget, hleft, hright, hparent⟩
    have hτσ : τ = σ :=
      hmin τ (1 + (m + k)) (by omega) hparent hτsub
    subst τ
    omega
  · exact hpop
  · rcases hpush with
      ⟨B, f, m, r, hr, τ, hlhs, hc, hrhs, hm_le, _hparentBudget,
        hτsub, hτlen, hchild, hparent⟩
    have hτσ : τ = σ :=
      hmin τ (1 + m) (by omega) hparent hτsub
    subst τ
    omega
  · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
    subst w
    subst n
    have hempty :
        g.DerivesIn 1 [ISym.indexed A (pref ++ [])]
          ([a].map fun b => (ISym.terminal b : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := 0) (A := A) (σ := pref ++ []) (w := [a])).mpr
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, rfl, rfl⟩
    have hempty_eq : ([] : List g.flag) = σ := by
      exact hmin [] 1 (by omega) (by simpa using hempty) (List.nil_sublist σ)
    have hσlen : σ.length = 0 := by
      simp [← hempty_eq]
    omega

/-- Prefix/suffix split for
`exists_bound_locally_budgeted_first_step_pop_of_suffix_minimal_long`. -/
theorem exists_bound_locally_budgeted_first_step_pop_cases_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ P →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          n + 1 ≤ N →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ n + 1 →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = [] ∧ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = f :: pref' ∧ pref'.length < pref.length ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_first_step_pop_of_suffix_minimal_long
      (g := g) hNF P N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hnN hwt hder hmin hlong
  obtain ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, hnBudget, hchild⟩ :=
    hK pref hpref n A σ w hnN hwt hder hmin hlong
  rcases append_eq_cons_cases (pref := pref) (σ := σ) (f := f) (ρ := ρ) hstack with
    hempty | hcons
  · rcases hempty with ⟨hpref, hσ⟩
    left
    exact ⟨f, ρ, B, r, hr, hpref, hσ, hlhs, hc, hrhs, hnBudget, hchild⟩
  · rcases hcons with ⟨pref', hpref, hρ⟩
    right
    subst pref
    subst ρ
    exact ⟨f, pref', B, r, hr, rfl, by simp, hlhs, hc, hrhs, hnBudget, hchild⟩

/-- Combined-budget split for the locally budgeted forced-pop lemma. In both pop branches the
recursive child has strictly smaller `live prefix length + derivation length`. -/
theorem exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (Q : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          pref.length + (n + 1) ≤ Q →
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ n + 1 →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = [] ∧ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n < Q ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = f :: pref' ∧
              pref'.length + n < Q ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_first_step_pop_cases_of_suffix_minimal_long
      (g := g) hNF Q Q target
  refine ⟨K, ?_⟩
  intro pref n A σ w hbudget hwt hder hmin hlong
  have hpref : pref.length ≤ Q := by omega
  have hnQ : n + 1 ≤ Q := by omega
  have hcases := hK pref hpref n A σ w hnQ hwt hder hmin hlong
  rcases hcases with hempty | hcons
  · rcases hempty with
      ⟨f, ρ, B, r, hr, hpref_eq, hσ, hlhs, hc, hrhs, _hnQ, hchild⟩
    left
    exact ⟨f, ρ, B, r, hr, hpref_eq, hσ, hlhs, hc, hrhs, by omega, hchild⟩
  · rcases hcons with
      ⟨f, pref', B, r, hr, hpref_eq, _hpref_lt, hlhs, hc, hrhs, _hnQ, hchild⟩
    right
    exact ⟨f, pref', B, r, hr, hpref_eq, by
      have hpref_len : pref.length = pref'.length + 1 := by
        simp [hpref_eq]
      omega, hlhs, hc, hrhs, hchild⟩

/-- Length-uniform form of
`exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long`.
One forced-pop threshold works for every target word of length at most `L`. -/
theorem
    exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            pref.length + (n + 1) ≤ Q →
            w <+ target →
            g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              m ≤ n + 1 →
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ <+ σ → τ = σ) →
            K < σ.length →
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = [] ∧ σ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                n < Q ∧
                g.DerivesIn n [ISym.indexed B ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym))) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = f :: pref' ∧
                pref'.length + n < Q ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))) := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long
        (g := g) hNF Q target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref n A σ w hbudget hwt hder hmin hlong
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long
        (g := g) hNF Q target)
  exact htarget pref n A σ w hbudget hwt hder hmin (lt_of_le_of_lt hle hlong)

/-- Slack form of the length-uniform locally budgeted combined-budget forced-pop split. -/
theorem
    exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long_target_length_with_slack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (Q L : ℕ) :
    ∃ K₀ : ℕ,
      ∀ K : ℕ,
        K₀ ≤ K →
        ∀ target : List T,
          target.length ≤ L →
          ∀ pref : List g.flag,
            ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
              pref.length + (n + 1) ≤ Q →
              w <+ target →
              g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              (∀ τ : List g.flag, ∀ m : ℕ,
                m ≤ n + 1 →
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                τ <+ σ → τ = σ) →
              K < σ.length →
              (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
                ∃ r ∈ g.rules,
                  pref = [] ∧ σ = f :: ρ ∧
                  r.lhs = A ∧ r.consume = some f ∧
                  r.rhs = [IRhsSymbol.nonterminal B none] ∧
                  n < Q ∧
                  g.DerivesIn n [ISym.indexed B ρ]
                    (w.map fun a => (ISym.terminal a : g.ISym))) ∨
              (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
                ∃ r ∈ g.rules,
                  pref = f :: pref' ∧
                  pref'.length + n < Q ∧
                  r.lhs = A ∧ r.consume = some f ∧
                  r.rhs = [IRhsSymbol.nonterminal B none] ∧
                  g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                    (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K₀, hK₀⟩ :=
    exists_bound_locally_budgeted_first_step_pop_combined_budget_cases_of_suffix_minimal_long_target_length
      (g := g) hNF Q L
  refine ⟨K₀, ?_⟩
  intro K hK target htargetLen pref n A σ w hbudget hwt hder hmin hlong
  exact hK₀ target htargetLen pref n A σ w hbudget hwt hder hmin
    (lt_of_le_of_lt hK hlong)

/-- A locally budget-minimal suffix under a bounded live prefix has bounded length. The
minimality budget is exactly the derivation length, so after a forced pop the child derivation
inherits the same invariant with one fewer step. -/
theorem exists_bound_locally_budgeted_minimal_suffix_length_of_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            m ≤ n →
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          pref.length + n ≤ N →
          σ.length ≤ K + N := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro pref hpref n A σ w _hwt hder _hmin hbudget
      have hn : n = 0 := by omega
      subst n
      cases w with
      | nil =>
          simp at hder
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hder
          | cons b rest =>
              simp at hder
  | succ N ih =>
      obtain ⟨Kprev, hprev⟩ := ih
      obtain ⟨Kpop, hpop⟩ :=
        exists_bound_locally_budgeted_first_step_pop_cases_of_suffix_minimal_long
          (g := g) hNF (N + 1) (N + 1) target
      refine ⟨max Kprev Kpop, ?_⟩
      intro pref hpref n A σ w hwt hder hmin hbudget
      by_cases hshort : σ.length ≤ max Kprev Kpop
      · omega
      have hlong : Kpop < σ.length := by omega
      cases n with
      | zero =>
          cases w with
          | nil =>
              simp at hder
          | cons a rest =>
              cases rest with
              | nil =>
                  simp at hder
              | cons b rest =>
                  simp at hder
      | succ n =>
          have hnN : n + 1 ≤ N + 1 := by omega
          have hcases :=
            hpop pref hpref n A σ w hnN hwt hder hmin hlong
          rcases hcases with hempty | hcons
          · rcases hempty with
              ⟨f, ρ, B, r, hr, hpref_eq, hσ, hlhs, hc, hrhs, _hnBudget, hchild⟩
            subst pref
            have hbudget_child : ([] : List g.flag).length + n ≤ N := by
              simp at hbudget ⊢
              omega
            have hmin_child :
                ∀ τ : List g.flag, ∀ m : ℕ,
                  m ≤ n →
                  g.DerivesIn m [ISym.indexed B (([] : List g.flag) ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  τ <+ ρ → τ = ρ := by
              intro τ m hm hτder hτsub
              have hparent0 :
                  g.DerivesIn (m + 1) [ISym.indexed A (f :: τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
                  (g := g) hNF (n := m) (A := A) (σ := f :: τ) (w := w)).mpr
                right
                left
                exact ⟨f, τ, B, r, hr, rfl, hlhs, hc, hrhs, by simpa using hτder⟩
              have hsub : (f :: τ) <+ σ := by
                simpa [hσ] using List.Sublist.cons_cons f hτsub
              have heq :=
                hmin (f :: τ) (m + 1) (by omega) (by simpa using hparent0) hsub
              have heq' : f :: τ = f :: ρ := by
                simpa [hσ] using heq
              exact (List.cons.inj heq').2
            have hρbound :=
              hprev ([] : List g.flag) (by simp) n B ρ w hwt
                (by simpa using hchild) hmin_child hbudget_child
            have hσlen : σ.length = ρ.length + 1 := by
              simp [hσ]
            omega
          · rcases hcons with
              ⟨f, pref', B, r, hr, hpref_eq, _hpref_lt, hlhs, hc, hrhs,
                _hnBudget, hchild⟩
            have hbudget_child : pref'.length + n ≤ N := by
              have hpref_len : pref.length = pref'.length + 1 := by
                simp [hpref_eq]
              omega
            have hpref'_le : pref'.length ≤ N := by omega
            have hmin_child :
                ∀ τ : List g.flag, ∀ m : ℕ,
                  m ≤ n →
                  g.DerivesIn m [ISym.indexed B (pref' ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  τ <+ σ → τ = σ := by
              intro τ m hm hτder hτsub
              have hparent0 :
                  g.DerivesIn (m + 1) [ISym.indexed A (f :: (pref' ++ τ))]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
                  (g := g) hNF (n := m) (A := A) (σ := f :: (pref' ++ τ))
                    (w := w)).mpr
                right
                left
                exact ⟨f, pref' ++ τ, B, r, hr, rfl, hlhs, hc, hrhs, hτder⟩
              have hparent :
                  g.DerivesIn (m + 1) [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                simpa [hpref_eq] using hparent0
              exact hmin τ (m + 1) (by omega) hparent hτsub
            have hσbound :=
              hprev pref' hpref'_le n B σ w hwt hchild hmin_child hbudget_child
            omega

/-- Local-budget bounded-prefix suffix shrinking. If the live prefix length plus the counted
derivation length is at most `N`, then a sub-suffix can be chosen with a uniform length bound;
the chosen suffix is minimal among all suffixes deriving the same yield within the original
local step budget. -/
theorem exists_bound_locally_budgeted_generating_prefixed_suffix_for_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          pref.length + n ≤ N →
          ∃ m : ℕ, ∃ τ : List g.flag,
            m ≤ n ∧
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) ∧
            τ <+ σ ∧
            τ.length ≤ K ∧
            ∀ ρ : List g.flag, ∀ k : ℕ,
              k ≤ n →
              g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              ρ <+ τ → ρ = τ := by
  obtain ⟨Kmin, hKmin⟩ :=
    exists_bound_locally_budgeted_minimal_suffix_length_of_bounded_prefix_budget
      (g := g) hNF N target
  refine ⟨Kmin + N, ?_⟩
  intro pref hpref n A σ w hwt hder hbudget
  let Y : Set (List g.flag) :=
    {τ : List g.flag |
      ∃ m : ℕ, m ≤ n ∧
        g.DerivesIn m [ISym.indexed A (pref ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym))}
  have hσY : σ ∈ Y := ⟨n, le_rfl, hder⟩
  obtain ⟨τ, hτmin, hτsub⟩ := exists_minimal_sublist g.flag Y σ hσY
  rcases hτmin.1 with ⟨m, hm_le_n, hτder⟩
  have hbudget_m : pref.length + m ≤ N := by omega
  have hlocal_min :
      ∀ ρ : List g.flag, ∀ k : ℕ,
        k ≤ m →
        g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ <+ τ → ρ = τ := by
    intro ρ k hk hρder hρsub
    exact hτmin.2 ρ ⟨k, le_trans hk hm_le_n, hρder⟩ hρsub
  have hτlen :=
    hKmin pref hpref m A τ w hwt hτder hlocal_min hbudget_m
  refine ⟨m, τ, hm_le_n, hτder, hτsub, hτlen, ?_⟩
  intro ρ k hk hρder hρsub
  exact hτmin.2 ρ ⟨k, hk, hρder⟩ hρsub

/-- Length-uniform version of
`exists_bound_locally_budgeted_generating_prefixed_suffix_for_bounded_prefix_budget`. For a
finite terminal alphabet, one bound works for every target word of length at most `L`. -/
theorem exists_bound_locally_budgeted_generating_prefixed_suffix_for_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            pref.length + n ≤ N →
            ∃ m : ℕ, ∃ τ : List g.flag,
              m ≤ n ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              τ <+ σ ∧
              τ.length ≤ K ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                k ≤ n →
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ <+ τ → ρ = τ := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_locally_budgeted_generating_prefixed_suffix_for_bounded_prefix_budget
        (g := g) hNF N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hbudget
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hspec :=
    Classical.choose_spec
      (exists_bound_locally_budgeted_generating_prefixed_suffix_for_bounded_prefix_budget
        (g := g) hNF N target)
  obtain ⟨m, τ, hm, hτder, hτsub, hτlen, hτmin⟩ :=
    hspec pref hpref n A σ w hwt hder hbudget
  refine ⟨m, τ, hm, hτder, hτsub, ?_, hτmin⟩
  exact le_trans hτlen
    (Finset.le_sup (s := targets) (f := targetBound) htargetMem)

/-- Whole-form budget-preserving suffix shrinker. Given a positionwise split of a sentential
form into singleton terminal derivations, shrink every indexed source stack to a bounded
substack while preserving the concatenated terminal yield and not increasing the total
singleton budget. Terminal source symbols are kept unchanged. -/
theorem exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ parts : List (ℕ × List T),
        (parts.flatMap fun p => p.2).length ≤ L →
        ∀ xs : List g.ISym,
          List.Forall₂
            (fun s p => g.DerivesIn p.1 [s]
              (p.2.map fun a => (ISym.terminal a : g.ISym)))
            xs parts →
          (∀ p ∈ parts, p.1 ≤ N) →
          ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
            (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
              (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
              List.Forall₂
                (fun s p => g.DerivesIn p.1 [s]
                  (p.2.map fun a => (ISym.terminal a : g.ISym)))
                ys parts' ∧
              List.Forall₂
                (fun s t =>
                  match s, t with
                  | ISym.terminal a, ISym.terminal b => a = b
                  | ISym.indexed A σ, ISym.indexed B τ =>
                      A = B ∧ τ <+ σ ∧ τ.length ≤ K
                  | _, _ => False)
                xs ys ∧
              parts'.length = parts.length ∧
              List.Forall₂
                (fun sp tq =>
                  match sp.1, tq.1 with
                  | ISym.terminal a, ISym.terminal b =>
                      a = b ∧ tq.2 = sp.2
                  | ISym.indexed A σ, ISym.indexed B τ =>
                      A = B ∧
                        tq.2.2 = sp.2.2 ∧
                        tq.2.1 ≤ sp.2.1 ∧
                        τ <+ σ ∧
                        τ.length ≤ K ∧
                        g.DerivesIn tq.2.1 [ISym.indexed B τ]
                          (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                        ∀ ρ : List g.flag, ∀ k : ℕ,
                          k ≤ sp.2.1 →
                          g.DerivesIn k [ISym.indexed B ρ]
                            (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                          ρ <+ τ → ρ = τ
                  | _, _ => False)
                (xs.zip parts) (ys.zip parts') ∧
              g.DerivesIn ((parts'.map fun p => p.1).sum) ys
                ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_generating_prefixed_suffix_for_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro parts hlen xs hparts hbudget
  revert hlen hbudget
  induction hparts with
  | nil =>
      intro _hlen _hbudget
      refine ⟨[], [], by simp, by simp, List.Forall₂.nil, List.Forall₂.nil,
        by simp, List.Forall₂.nil, ?_⟩
      simp
  | cons hhead _htail ih =>
      intro hlen hbudget
      rename_i s p xs parts
      have htailLen : (parts.flatMap fun p => p.2).length ≤ L := by
        have hsub :
            (parts.flatMap fun p => p.2).Sublist
              ((p :: parts).flatMap fun p => p.2) := by
          simp only [List.flatMap_cons]
          exact List.sublist_append_right p.2 (parts.flatMap fun p => p.2)
        exact le_trans hsub.length_le hlen
      have htailBudget : ∀ q ∈ parts, q.1 ≤ N := by
        intro q hq
        exact hbudget q (by simp [hq])
      obtain ⟨ys, parts', hsum, hflat, hparts', hrel, hpartsLen', hcert, hder⟩ :=
        ih htailLen htailBudget
      cases s with
      | terminal a =>
          refine ⟨ISym.terminal a :: ys, p :: parts', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hsum]
          · simp [hflat]
          · exact List.Forall₂.cons hhead hparts'
          · exact List.Forall₂.cons rfl hrel
          · simp [hpartsLen']
          ·
            exact List.Forall₂.cons ⟨rfl, rfl⟩ hcert
          ·
            have hcomposed :=
              derivesIn_symbols_to_terminals_of_forall₂
                (g := g) (List.Forall₂.cons hhead hparts')
            simpa [hflat, List.map_append] using hcomposed
      | indexed A σ =>
          have hheadBudget : p.1 ≤ N := hbudget p (by simp)
          have hpieceSub :
              p.2.Sublist ((p :: parts).flatMap fun p => p.2) := by
            simp only [List.flatMap_cons]
            exact List.sublist_append_left p.2 (parts.flatMap fun p => p.2)
          obtain ⟨m, τ, hm, hτder, hτsub, hτlen, hτmin⟩ :=
            hK ((p :: parts).flatMap fun p => p.2) hlen
              ([] : List g.flag) (by simp) p.1 A σ p.2 hpieceSub
              (by simpa using hhead) (by simpa using hheadBudget)
          have hτder' :
              g.DerivesIn m [ISym.indexed A τ]
                (p.2.map fun a => (ISym.terminal a : g.ISym)) := by
            simpa using hτder
          have hpartsNew :
              List.Forall₂
              (fun s p => g.DerivesIn p.1 [s]
                  (p.2.map fun a => (ISym.terminal a : g.ISym)))
                (ISym.indexed A τ :: ys) (((m, p.2) : ℕ × List T) :: parts') :=
            List.Forall₂.cons hτder' hparts'
          refine ⟨ISym.indexed A τ :: ys, (m, p.2) :: parts', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          ·
            simp
            omega
          · simp [hflat]
          · exact hpartsNew
          · exact List.Forall₂.cons ⟨rfl, hτsub, hτlen⟩ hrel
          · simp [hpartsLen']
          ·
            refine List.Forall₂.cons ?_ hcert
            refine ⟨rfl, rfl, hm, hτsub, hτlen, hτder', ?_⟩
            intro ρ k hk hρder hρsub
            exact hτmin ρ k hk (by simpa using hρder) hρsub
          ·
            have hcomposed :=
              derivesIn_symbols_to_terminals_of_forall₂
                (g := g) hpartsNew
            simpa [hflat, List.map_append] using hcomposed

/-- Whole-form budget-preserving suffix shrinker. Given a positionwise split of a sentential
form into singleton terminal derivations, shrink every indexed source stack to a bounded
substack while preserving the concatenated terminal yield and not increasing the total
singleton budget. Terminal source symbols are kept unchanged. -/
theorem exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ parts : List (ℕ × List T),
        (parts.flatMap fun p => p.2).length ≤ L →
        ∀ xs : List g.ISym,
          List.Forall₂
            (fun s p => g.DerivesIn p.1 [s]
              (p.2.map fun a => (ISym.terminal a : g.ISym)))
            xs parts →
          (∀ p ∈ parts, p.1 ≤ N) →
          ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
            (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
              (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
              List.Forall₂
                (fun s p => g.DerivesIn p.1 [s]
                  (p.2.map fun a => (ISym.terminal a : g.ISym)))
                ys parts' ∧
              List.Forall₂
                (fun s t =>
                  match s, t with
                  | ISym.terminal a, ISym.terminal b => a = b
                  | ISym.indexed A σ, ISym.indexed B τ =>
                      A = B ∧ τ <+ σ ∧ τ.length ≤ K
                  | _, _ => False)
                xs ys ∧
              g.DerivesIn ((parts'.map fun p => p.1).sum) ys
                ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro parts hlen xs hparts hbudget
  obtain ⟨ys, parts', hsum, hflat, hparts', hrel, _hpartsLen', _hcert, hder⟩ :=
    hK parts hlen xs hparts hbudget
  exact ⟨ys, parts', hsum, hflat, hparts', hrel, hder⟩

/-- Trace-level form of
`exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget_with_minimality`.
Besides the replacement sentential form, it exposes the original singleton split of the trace
suffix and the per-position certificate saying that each indexed replacement is locally
sublist-minimal for the same terminal slice and original local step budget. -/
theorem exists_bound_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ parts : List (ℕ × List T),
            ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
              parts.length = (trace.get ⟨i, hi⟩).length ∧
                (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
                (parts.flatMap fun p => p.2) = target ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  (trace.get ⟨i, hi⟩) parts ∧
                (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
                (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  ys parts' ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed B τ =>
                        A = B ∧ τ <+ σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                parts'.length = parts.length ∧
                List.Forall₂
                  (fun sp tq =>
                    match sp.1, tq.1 with
                    | ISym.terminal a, ISym.terminal b =>
                        a = b ∧ tq.2 = sp.2
                    | ISym.indexed A σ, ISym.indexed B τ =>
                        A = B ∧
                          tq.2.2 = sp.2.2 ∧
                          tq.2.1 ≤ sp.2.1 ∧
                          τ <+ σ ∧
                          τ.length ≤ K ∧
                          g.DerivesIn tq.2.1 [ISym.indexed B τ]
                            (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                          ∀ ρ : List g.flag, ∀ k : ℕ,
                            k ≤ sp.2.1 →
                            g.DerivesIn k [ISym.indexed B ρ]
                              (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                            ρ <+ τ → ρ = τ
                    | _, _ => False)
                  ((trace.get ⟨i, hi⟩).zip parts) (ys.zip parts') ∧
                g.DerivesIn ((parts'.map fun p => p.1).sum) ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, hpartsLen, hsum, hflat, hparts⟩ :=
    accepting_derivationTrace_symbols_suffix_to_terminals_split
      (g := g) htrace hlast hi
  have hflatLen : (parts.flatMap fun p => p.2).length ≤ L := by
    simpa [hflat] using htargetLen
  have hpart_le_sum_all :
      ∀ l : List (ℕ × List T), ∀ p ∈ l, p.1 ≤ (l.map fun q => q.1).sum := by
    intro l
    induction l with
    | nil =>
        intro p hp
        simp at hp
    | cons =>
        rename_i r rest ihl
        intro p hp
        simp only [List.mem_cons] at hp
        simp
        rcases hp with hp_eq | hp
        · subst p
          exact Nat.le_add_right r.1 ((rest.map fun q => q.1).sum)
        · exact le_trans (ihl p hp) (Nat.le_add_left ((rest.map fun q => q.1).sum) r.1)
  have hpart_le_sum : ∀ p ∈ parts, p.1 ≤ (parts.map fun q => q.1).sum :=
    hpart_le_sum_all parts
  have hbudgetParts : ∀ p ∈ parts, p.1 ≤ N := by
    intro p hp
    exact le_trans (hpart_le_sum p hp) (by omega)
  obtain ⟨ys, parts', hsum', hflat', hparts', hrel, hpartsLen', hcert, hder⟩ :=
    hK parts hflatLen (trace.get ⟨i, hi⟩) hparts hbudgetParts
  refine ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, ?_⟩
  simpa [hflat] using hder

/-- Accepting-trace wrapper for the whole-form budget-preserving suffix shrinker. At a trace
position whose remaining suffix has budget at most `N`, every indexed stack in the displayed
sentential form can be replaced by a bounded substack while preserving a derivation to the
same target word with no more remaining steps. -/
theorem exists_bound_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ ys : List g.ISym, ∃ n' : ℕ,
              n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed B τ =>
                        A = B ∧ τ <+ σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                g.DerivesIn n' ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_derivesIn_symbols_to_terminals_shrink_stacks_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, _hpartsLen, hsum, hflat, hparts⟩ :=
    accepting_derivationTrace_symbols_suffix_to_terminals_split
      (g := g) htrace hlast hi
  have hflatLen : (parts.flatMap fun p => p.2).length ≤ L := by
    simpa [hflat] using htargetLen
  have hpart_le_sum_all :
      ∀ l : List (ℕ × List T), ∀ p ∈ l, p.1 ≤ (l.map fun q => q.1).sum := by
    intro l
    induction l with
    | nil =>
        intro p hp
        simp at hp
    | cons =>
        rename_i r rest ihl
        intro p hp
        simp only [List.mem_cons] at hp
        simp
        rcases hp with hp_eq | hp
        · subst p
          exact Nat.le_add_right r.1 ((rest.map fun q => q.1).sum)
        · exact le_trans (ihl p hp) (Nat.le_add_left ((rest.map fun q => q.1).sum) r.1)
  have hpart_le_sum : ∀ p ∈ parts, p.1 ≤ (parts.map fun q => q.1).sum :=
    hpart_le_sum_all parts
  have hbudgetParts : ∀ p ∈ parts, p.1 ≤ N := by
    intro p hp
    exact le_trans (hpart_le_sum p hp) (by omega)
  obtain ⟨ys, parts', hsum', _hflat', _hparts', hrel, hder⟩ :=
    hK parts hflatLen (trace.get ⟨i, hi⟩) hparts hbudgetParts
  refine ⟨ys, (parts'.map fun p => p.1).sum, ?_, hrel, ?_⟩
  · omega
  · simpa [hflat] using hder

/-- Budget-preserving context replacement form of the trace-local shrinker. If the local
future derivation of the distinguished indexed symbol fits inside the combined live-prefix and
step budget `N`, then the shrunk replacement of the whole trace suffix has no more steps than
the original suffix from that trace position. -/
theorem exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              pref.length ≤ N →
              pref.length + (trace.length - 1 - i) ≤ N →
              ∀ u v : List g.ISym,
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                ∃ q m : ℕ, ∃ τ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                  w <+ target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ <+ σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  ∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_generating_prefixed_suffix_for_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi A pref σ hpref hbudget u v hctx
  obtain ⟨nu, ns, nv, wu, w, wv, hsum, hw, hwt, hu, hlocal, hv⟩ :=
    accepting_derivationTrace_indexed_context_suffix_to_terminals_split
      (g := g) htrace hlast hi hctx
  have hns_le_suffix : ns ≤ trace.length - 1 - i := by omega
  have hlocalBudget : pref.length + ns ≤ N := by omega
  obtain ⟨m, τ, hm, hτder, hτsub, hτlen, hτmin⟩ :=
    hK target htargetLen pref hpref ns A σ w hwt hlocal hlocalBudget
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  have hreplacement :
      g.DerivesIn (nu + m + nv) (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    have hcomp :=
      derivesIn_context_indexed_to_terminals_of_derivesIn
        (g := g) (u := u) (v := v) (A := A) (σ := pref ++ τ)
        (nu := nu) (ns := m) (nv := nv)
        (wu := wu) (ws := w) (wv := wv) hu hτder hv
    simpa [hw] using hcomp
  have hm_suffix : m ≤ trace.length - 1 - i := by omega
  have hrepl_suffix : nu + m + nv ≤ trace.length - 1 - i := by omega
  refine ⟨ns, m, τ, w, nu + m + nv, hwt, hwlen, hns_le_suffix, hm,
    hm_suffix, hrepl_suffix, hτsub, hτlen, hτder, hreplacement, ?_⟩
  intro ρ k hk hρder hρsub
  exact hτmin ρ k hk hρder hρsub

/-- Membership-facing budget-preserving context replacement. This packages the context split
around the selected indexed symbol together with the no-longer-than-original replacement of
the accepting trace suffix. -/
theorem exists_bound_accepting_derivationTrace_indexed_mem_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              pref.length ≤ N →
              pref.length + (trace.length - 1 - i) ≤ N →
              ISym.indexed A (pref ++ σ) ∈ trace.get ⟨i, hi⟩ →
              ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ τ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                w <+ target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi A pref σ hpref hbudget hmem
  rcases (List.mem_iff_append.mp hmem) with ⟨u, v, hctx0⟩
  have hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v := by
    simpa using hctx0
  obtain ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
      hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hpref hbudget u v hctx
  exact ⟨u, v, q, m, τ, w, n', hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
    hτsub, hτlen, hτder, hreplacement, hτmin⟩

/-- Max-stack budget-preserving replacement. At a trace position with positive maximum stack
height, choose a symbol attaining that maximum, split its stack after `P` flags, shrink the
remaining suffix, and replace the whole accepting trace suffix without increasing its length. -/
theorem exists_bound_accepting_derivationTrace_max_stack_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            P ≤ Q →
            P + (trace.length - 1 - i) ≤ Q →
            0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
            ∃ A : g.nt, ∃ η pref σ τ : List g.flag,
              ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                η = pref ++ σ ∧
                pref.length ≤ P ∧
                η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                w <+ target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_mem_suffix_shrink_replacement_budget
      (g := g) hNF Q L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hPQ hbudget hpos
  obtain ⟨A, η, hmem, hηmax⟩ :=
    exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
      (g := g) (w := trace.get ⟨i, hi⟩) hpos
  let pref : List g.flag := η.take P
  let σ : List g.flag := η.drop P
  have hη : η = pref ++ σ := by
    unfold pref σ
    exact (List.take_append_drop P η).symm
  have hprefP : pref.length ≤ P := by
    unfold pref
    exact List.length_take_le P η
  have hprefQ : pref.length ≤ Q := le_trans hprefP hPQ
  have hlocalBudget : pref.length + (trace.length - 1 - i) ≤ Q := by omega
  have hmem' : ISym.indexed A (pref ++ σ) ∈ trace.get ⟨i, hi⟩ := by
    simpa [← hη] using hmem
  obtain ⟨u, v, q, m, τ, w, n', hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hprefQ hlocalBudget hmem'
  exact ⟨A, η, pref, σ, τ, u, v, q, m, w, n', hmem, hη, hprefP, hηmax, hctx,
    hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin⟩

/-- Canonical max-stack replacement. This strengthens
`exists_bound_accepting_derivationTrace_max_stack_suffix_shrink_replacement_budget` by
recording that the selected maximum stack is split as `η.take P ++ η.drop P`. The stronger
fields are needed by the bounded-prefix reachability argument, where only this canonical
split has a finite-surface interpretation. -/
theorem exists_bound_accepting_derivationTrace_canonical_max_stack_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            P ≤ Q →
            P + (trace.length - 1 - i) ≤ Q →
            0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
            ∃ A : g.nt, ∃ η pref σ τ : List g.flag,
              ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                η = pref ++ σ ∧
                pref = η.take P ∧
                σ = η.drop P ∧
                pref.length ≤ P ∧
                (P < η.length → pref.length = P) ∧
                η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                w <+ target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ <+ σ ∧ τ.length ≤ K ∧
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_mem_suffix_shrink_replacement_budget
      (g := g) hNF Q L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hPQ hbudget hpos
  obtain ⟨A, η, hmem, hηmax⟩ :=
    exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
      (g := g) (w := trace.get ⟨i, hi⟩) hpos
  let pref : List g.flag := η.take P
  let σ : List g.flag := η.drop P
  have hη : η = pref ++ σ := by
    unfold pref σ
    exact (List.take_append_drop P η).symm
  have hprefP : pref.length ≤ P := by
    unfold pref
    exact List.length_take_le P η
  have hprefEq : pref = η.take P := rfl
  have hσEq : σ = η.drop P := rfl
  have hprefLen_eq_of_lt : P < η.length → pref.length = P := by
    intro hlt
    simp [pref, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hprefQ : pref.length ≤ Q := le_trans hprefP hPQ
  have hlocalBudget : pref.length + (trace.length - 1 - i) ≤ Q := by omega
  have hmem' : ISym.indexed A (pref ++ σ) ∈ trace.get ⟨i, hi⟩ := by
    simpa [← hη] using hmem
  obtain ⟨u, v, q, m, τ, w, n', hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hprefQ hlocalBudget hmem'
  exact ⟨A, η, pref, σ, τ, u, v, q, m, w, n', hmem, hη, hprefEq, hσEq,
    hprefP, hprefLen_eq_of_lt, hηmax, hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
    hτsub, hτlen, hτder, hreplacement, hτmin⟩

/-- A compact counted first-step shrinking corollary. Under a bounded live prefix, every
non-pop, non-terminal first step can be replaced by a counted derivation from a bounded
sub-suffix of the original stack; pop and terminal cases are exposed separately. -/
theorem exists_bound_counted_parent_shrink_or_pop_or_terminal_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∃ m : ℕ, ∃ τ : List g.flag,
              τ <+ σ ∧ τ.length ≤ K ∧
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n < n + 1 ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a] ∧ n = 0) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_rule_binary_push_bounded_prefix_suffix_with_parent_for_target_sublists
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder
  have hcases := hK pref hpref n A σ w hwt hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, τ, _hlhs, _hc, _hrhs, _hw,
        _hupos, _hvpos, _hult, _hvlt, _husub, _hvsub, hτsub, hτlen,
        _hleft, _hright, hparent⟩
    left
    exact ⟨1 + (m + k), τ, hτsub, hτlen, hparent⟩
  · right
    left
    exact hpop
  · rcases hpush with
      ⟨B, f, m, r, hr, τ, _hlhs, _hc, _hrhs, _hn, hτsub, hτlen, _hchild, hparent⟩
    left
    exact ⟨1 + m, τ, hτsub, hτlen, hparent⟩
  · right
    right
    exact hterm

/-- If the visible suffix of a prefixed stack is chosen sublist-minimal among counted
derivations of the same yield, and that suffix is longer than the uniform shrinking bound, then
the first step cannot be binary, push, or terminal. Hence it must be a pop step. -/
theorem exists_bound_first_step_pop_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          ∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n < n + 1 ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_parent_shrink_or_pop_or_terminal_for_target_sublists
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hmin hlong
  have hcases := hK pref hpref n A σ w hwt hder
  rcases hcases with hshrink | hpop | hterm
  · rcases hshrink with ⟨m, τ, hτsub, hτlen, hτder⟩
    have hτσ : τ = σ := hmin τ m hτder hτsub
    subst τ
    omega
  · exact hpop
  · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
    subst w
    have hempty :
        g.DerivesIn 1 [ISym.indexed A (pref ++ [])]
          ([a].map fun b => (ISym.terminal b : g.ISym)) := by
      apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
        (g := g) hNF (n := 0) (A := A) (σ := pref ++ []) (w := [a])).mpr
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, rfl, rfl⟩
    have hempty_eq : ([] : List g.flag) = σ := by
      exact hmin [] 1 (by simpa using hempty) (List.nil_sublist σ)
    have hσlen : σ.length = 0 := by
      simp [← hempty_eq]
    omega

/-- Prefix/suffix form of `exists_bound_first_step_pop_of_suffix_minimal_long`. If a
sublist-minimal visible suffix is too long, the forced pop either consumes the suffix head
(`pref = []`) or consumes one symbol from the live prefix and leaves the suffix untouched under
a strictly shorter prefix. -/
theorem exists_bound_first_step_pop_cases_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = [] ∧ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = f :: pref' ∧ pref'.length < pref.length ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_first_step_pop_of_suffix_minimal_long
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hmin hlong
  obtain ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, _hn, hchild⟩ :=
    hK pref hpref n A σ w hwt hder hmin hlong
  rcases append_eq_cons_cases (pref := pref) (σ := σ) (f := f) (ρ := ρ) hstack with
    hempty | hpref
  · rcases hempty with ⟨hpref, hσ⟩
    left
    exact ⟨f, ρ, B, r, hr, hpref, hσ, hlhs, hc, hrhs, hchild⟩
  · rcases hpref with ⟨pref', hpref, hρ⟩
    right
    subst pref
    subst ρ
    exact ⟨f, pref', B, r, hr, rfl, by simp, hlhs, hc, hrhs, hchild⟩

/-- Length-uniform prefix/suffix forced-pop split for globally minimal suffixes. One bound
works for every target word of length at most `L`. -/
theorem exists_bound_first_step_pop_cases_of_suffix_minimal_long_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ <+ σ → τ = σ) →
            K < σ.length →
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = [] ∧ σ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                g.DerivesIn n [ISym.indexed B ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym))) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = f :: pref' ∧ pref'.length < pref.length ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))) := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_first_step_pop_cases_of_suffix_minimal_long
        (g := g) hNF N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin hlong
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (exists_bound_first_step_pop_cases_of_suffix_minimal_long
        (g := g) hNF N target)
  exact htarget pref hpref n A σ w hwt hder hmin (lt_of_le_of_lt hle hlong)

/-- Budgeted form of `exists_bound_first_step_pop_of_suffix_minimal_long`. The forced pop
either consumes the first symbol of the visible suffix, leaving the step budget below `N`, or
it consumes one live-prefix symbol and strictly decreases the combined prefix/step budget. -/
theorem exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          K < σ.length →
          pref.length + (n + 1) ≤ N →
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = [] ∧ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              n ≤ N ∧
              g.DerivesIn n [ISym.indexed B ρ]
                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              pref = f :: pref' ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              pref'.length + n ≤ N ∧
              g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_first_step_pop_of_suffix_minimal_long
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hmin hlong hbudget
  obtain ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, _hn, hchild⟩ :=
    hK pref hpref n A σ w hwt hder hmin hlong
  rcases pop_prefix_suffix_budget_cases (g := g) (N := N) (n := n)
      (pref := pref) (σ := σ) (f := f) (ρ := ρ) hbudget hstack with
    hempty | hcons
  · rcases hempty with ⟨hpref, hσ, hnN⟩
    left
    exact ⟨f, ρ, B, r, hr, hpref, hσ, hlhs, hc, hrhs, hnN, hchild⟩
  · rcases hcons with ⟨pref', hpref, hρ, hbudget'⟩
    right
    exact ⟨f, pref', B, r, hr, hpref, hlhs, hc, hrhs, hbudget',
      by simpa [hρ] using hchild⟩

/-- Length-uniform budgeted forced-pop split. One bound works for every target word whose
length is at most `L`. -/
theorem exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ <+ σ → τ = σ) →
            K < σ.length →
            pref.length + (n + 1) ≤ N →
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = [] ∧ σ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                n ≤ N ∧
                g.DerivesIn n [ISym.indexed B ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym))) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = f :: pref' ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                pref'.length + n ≤ N ∧
                g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))) := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long
        (g := g) hNF N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin hlong hbudget
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long
        (g := g) hNF N target)
  exact htarget pref hpref n A σ w hwt hder hmin (lt_of_le_of_lt hle hlong) hbudget

/-- Slack form of
`exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long_target_length`: any larger
threshold than the uniform one can be used in the forced-pop conclusion. -/
theorem exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long_target_length_with_slack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K₀ : ℕ,
      ∀ K : ℕ,
        K₀ ≤ K →
        ∀ target : List T,
          target.length ≤ L →
          ∀ pref : List g.flag,
            pref.length ≤ N →
            ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
              w <+ target →
              g.DerivesIn (n + 1) [ISym.indexed A (pref ++ σ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              (∀ τ : List g.flag, ∀ m : ℕ,
                g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                τ <+ σ → τ = σ) →
              K < σ.length →
              pref.length + (n + 1) ≤ N →
              (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
                ∃ r ∈ g.rules,
                  pref = [] ∧ σ = f :: ρ ∧
                  r.lhs = A ∧ r.consume = some f ∧
                  r.rhs = [IRhsSymbol.nonterminal B none] ∧
                  n ≤ N ∧
                  g.DerivesIn n [ISym.indexed B ρ]
                    (w.map fun a => (ISym.terminal a : g.ISym))) ∨
              (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
                ∃ r ∈ g.rules,
                  pref = f :: pref' ∧
                  r.lhs = A ∧ r.consume = some f ∧
                  r.rhs = [IRhsSymbol.nonterminal B none] ∧
                  pref'.length + n ≤ N ∧
                  g.DerivesIn n [ISym.indexed B (pref' ++ σ)]
                    (w.map fun a => (ISym.terminal a : g.ISym))) := by
  obtain ⟨K₀, hK₀⟩ :=
    exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long_target_length
      (g := g) hNF N L
  refine ⟨K₀, ?_⟩
  intro K hK target htargetLen pref hpref n A σ w hwt hder hmin hlong hbudget
  exact hK₀ target htargetLen pref hpref n A σ w hwt hder hmin
    (lt_of_le_of_lt hK hlong) hbudget

/-- A counted sublist-minimal suffix under a bounded live prefix has bounded length. The bound
is obtained by induction on the combined live-prefix/step budget: if the suffix is longer than
the uniform first-step shrinking bound, the first step is forced to be a pop, and the child
derivation inherits the same sublist-minimality with a strictly smaller budget. -/
theorem exists_bound_counted_minimal_suffix_length_of_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ τ : List g.flag, ∀ m : ℕ,
            g.DerivesIn m [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            τ <+ σ → τ = σ) →
          pref.length + n ≤ N →
          σ.length ≤ K + N := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro pref hpref n A σ w _hwt hder _hmin hbudget
      have hn : n = 0 := by omega
      subst n
      cases w with
      | nil =>
          simp at hder
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hder
          | cons b rest =>
              simp at hder
  | succ N ih =>
      obtain ⟨Kprev, hprev⟩ := ih
      obtain ⟨Kpop, hpop⟩ :=
        exists_bound_first_step_pop_budget_cases_of_suffix_minimal_long
          (g := g) hNF (N + 1) target
      refine ⟨max Kprev Kpop, ?_⟩
      intro pref hpref n A σ w hwt hder hmin hbudget
      by_cases hshort : σ.length ≤ max Kprev Kpop
      · omega
      have hlong : Kpop < σ.length := by omega
      cases n with
      | zero =>
          cases w with
          | nil =>
              simp at hder
          | cons a rest =>
              cases rest with
              | nil =>
                  simp at hder
              | cons b rest =>
                  simp at hder
      | succ n =>
          have hcases :=
            hpop pref hpref n A σ w hwt hder hmin hlong hbudget
          rcases hcases with hempty | hcons
          · rcases hempty with
              ⟨f, ρ, B, r, hr, hpref_eq, hσ, hlhs, hc, hrhs, _hnN, hchild⟩
            subst pref
            have hbudget_child : ([] : List g.flag).length + n ≤ N := by
              simp at hbudget ⊢
              omega
            have hmin_child :
                ∀ τ : List g.flag, ∀ m : ℕ,
                  g.DerivesIn m [ISym.indexed B (([] : List g.flag) ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  τ <+ ρ → τ = ρ := by
              intro τ m hτder hτsub
              have hparent0 :
                  g.DerivesIn (m + 1) [ISym.indexed A (f :: τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
                  (g := g) hNF (n := m) (A := A) (σ := f :: τ) (w := w)).mpr
                right
                left
                exact ⟨f, τ, B, r, hr, rfl, hlhs, hc, hrhs, by simpa using hτder⟩
              have hsub : (f :: τ) <+ σ := by
                simpa [hσ] using List.Sublist.cons_cons f hτsub
              have heq := hmin (f :: τ) (m + 1) (by simpa using hparent0) hsub
              have heq' : f :: τ = f :: ρ := by
                simpa [hσ] using heq
              exact (List.cons.inj heq').2
            have hρbound :=
              hprev ([] : List g.flag) (by simp) n B ρ w hwt
                (by simpa using hchild) hmin_child hbudget_child
            have hσlen : σ.length = ρ.length + 1 := by
              simp [hσ]
            omega
          · rcases hcons with
              ⟨f, pref', B, r, hr, hpref_eq, hlhs, hc, hrhs, _hbudget', hchild⟩
            have hbudget_child : pref'.length + n ≤ N := by
              have hpref_len : pref.length = pref'.length + 1 := by
                simp [hpref_eq]
              omega
            have hpref'_le : pref'.length ≤ N := by omega
            have hmin_child :
                ∀ τ : List g.flag, ∀ m : ℕ,
                  g.DerivesIn m [ISym.indexed B (pref' ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  τ <+ σ → τ = σ := by
              intro τ m hτder hτsub
              have hparent0 :
                  g.DerivesIn (m + 1) [ISym.indexed A (f :: (pref' ++ τ))]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
                  (g := g) hNF (n := m) (A := A) (σ := f :: (pref' ++ τ))
                    (w := w)).mpr
                right
                left
                exact ⟨f, pref' ++ τ, B, r, hr, rfl, hlhs, hc, hrhs, hτder⟩
              have hparent :
                  g.DerivesIn (m + 1) [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) := by
                simpa [hpref_eq] using hparent0
              exact hmin τ (m + 1) hparent hτsub
            have hσbound :=
              hprev pref' hpref'_le n B σ w hwt hchild hmin_child hbudget_child
            omega

/-- Length-uniform version of
`exists_bound_counted_minimal_suffix_length_of_bounded_prefix_budget`. For a finite terminal
alphabet, one suffix-height bound works for every target word of length at most `L`, provided
the suffix is globally sublist-minimal for its prefixed nonterminal/yield under a derivation
whose live-prefix/step budget is at most `N`. -/
theorem exists_bound_counted_minimal_suffix_length_of_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ <+ σ → τ = σ) →
            pref.length + n ≤ N →
            σ.length ≤ K + N := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_counted_minimal_suffix_length_of_bounded_prefix_budget
        (g := g) hNF N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin hbudget
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have hspec :=
    Classical.choose_spec
      (exists_bound_counted_minimal_suffix_length_of_bounded_prefix_budget
        (g := g) hNF N target)
  have hσ :=
    hspec pref hpref n A σ w hwt hder hmin hbudget
  exact le_trans hσ (Nat.add_le_add_right hle N)

end IndexedGrammar
