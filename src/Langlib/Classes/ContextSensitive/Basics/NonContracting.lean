module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive
public import Langlib.Grammars.ContextSensitive.Basic.FiniteNT
public import Langlib.Grammars.Unrestricted.Toolbox
import Mathlib.Tactic
@[expose]
public section



/-! # ε-elimination of context-sensitive grammars

Every context-sensitive language (in the broad `S → ε`-optional `grammar_context_sensitive`
sense) admits an equivalent — off the empty word — **non-contracting** grammar with finitely many
nonterminals (`exists_noncontracting_offEmpty_of_CS`). This is the structural normal form used,
e.g., in the `CS = LBA` (Kuroda) construction and in establishing `CS ⊆ Recursive`.

## Strategy

With the standard definition of `grammar_context_sensitive`, the start symbol `S`
never occurs on a right-hand side once the optional `S → ε` rule is present. This makes
ε-elimination **elementary**: simply delete every contracting rule (i.e. keep only the
non-contracting ones). Concretely, set

```
g' := { nt := g.nt, initial := g.initial,
        rules := g.rules.filter (fun r => decide (grule_noncontracting r)) }.
```

`g'` is non-contracting by construction, and `grammar_language g' = grammar_language g \ {[]}`.
The non-obvious inclusion is `⊇`: starting from the single start symbol `[S]` (with the target
word `≠ []`), the very first rule fired has empty context and `input_N = S`; it cannot be the
`S → ε` rule (that yields `[]`, which is stuck), so it is non-contracting and its output is
`S`-free (by `initial_not_on_rhs`). From there every sentential form stays `S`-free, and on
an `S`-free form the matched rule is never the `S → ε` rule, hence non-contracting and kept in
`g'`. So the whole `g`-derivation is in fact a `g'`-derivation.

## Main declarations

* `exists_noncontracting_offEmpty_of_CS`
-/

open Relation

variable {T : Type}

/-- The ε-free grammar obtained by deleting every contracting rule of `g`. -/
private def gFilter (g : grammar T) : grammar T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.filter
    (fun r => decide (r.input_L.length + 1 + r.input_R.length ≤ r.output_string.length))

@[simp] private lemma gFilter_nt (g : grammar T) : (gFilter g).nt = g.nt := rfl
@[simp] private lemma gFilter_initial (g : grammar T) : (gFilter g).initial = g.initial := rfl

private lemma mem_gFilter_rules {g : grammar T} {r : grule T g.nt} :
    r ∈ (gFilter g).rules ↔ r ∈ g.rules ∧ grule_noncontracting r := by
  show r ∈ g.rules.filter _ ↔ _
  rw [List.mem_filter]
  simp only [decide_eq_true_eq, grule_noncontracting, ge_iff_le]

/-- `gFilter g` is non-contracting. -/
private lemma gFilter_noncontracting (g : grammar T) :
    grammar_noncontracting (gFilter g) := by
  intro r hr
  exact (mem_gFilter_rules.mp hr).2

/-- A non-contracting derivation does not decrease length. -/
private lemma nc_derives_length_le {g : grammar T} (hnc : grammar_noncontracting g)
    {a b : List (symbol T g.nt)} (h : grammar_derives g a b) : a.length ≤ b.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih => exact le_trans ih (noncontracting_transforms_length_le g hnc hs)

/-- Every `gFilter`-transform step is a `g`-transform step (the rules are a sublist). -/
private lemma gFilter_transforms (g : grammar T) {a b : List (symbol T g.nt)}
    (h : grammar_transforms (gFilter g) a b) : grammar_transforms g a b := by
  obtain ⟨r, hr, u, v, hbef, haft⟩ := h
  exact ⟨r, (mem_gFilter_rules.mp hr).1, u, v, hbef, haft⟩

/-- If every rule of `g` is non-contracting then `gFilter g` keeps them all, so every
`g`-derivation is a `gFilter g`-derivation. -/
private lemma gFilter_derives_of_allNC (g : grammar T)
    (hall : ∀ r ∈ g.rules, grule_noncontracting r) {a b : List (symbol T g.nt)}
    (h : grammar_derives g a b) : grammar_derives (gFilter g) a b := by
  induction h with
  | refl => exact grammar_deri_self
  | tail _ hs ih =>
      obtain ⟨r', hr', u, v, hbef, haft⟩ := hs
      exact grammar_deri_of_deri_tran ih
        ⟨r', mem_gFilter_rules.mpr ⟨hr', hall r' hr'⟩, u, v, hbef, haft⟩

/-- Every `gFilter`-derivation is a `g`-derivation. -/
private lemma gFilter_derives (g : grammar T) {a b : List (symbol T g.nt)}
    (h : grammar_derives (gFilter g) a b) : grammar_derives g a b := by
  induction h with
  | refl => exact grammar_deri_self
  | tail _ hstep ih =>
      exact grammar_deri_of_deri_tran ih (gFilter_transforms g hstep)

/-- **The `S`-free invariant (Lemma B).** Assume the start symbol never occurs on a
right-hand side (`hrhs`). If `α` does not contain the start symbol and `g` transforms `α`
into `β`, then the rule used is non-contracting (so it survives the filter, giving a
`gFilter g`-step), and `β` is again `S`-free. -/
private lemma sFree_step (g : grammar T) (hg : grammar_context_sensitive g)
    (hrhs : initial_not_on_rhs g) {α β : List (symbol T g.nt)}
    (hS : symbol.nonterminal g.initial ∉ α)
    (h : grammar_transforms g α β) :
    grammar_transforms (gFilter g) α β ∧ symbol.nonterminal g.initial ∉ β := by
  obtain ⟨r, hr, u, v, hbef, haft⟩ := h
  -- The matched `[nonterminal r.input_N]` sits inside `α`, which is `S`-free, so `input_N ≠ S`.
  have hNmem : symbol.nonterminal r.input_N ∈ α := by
    rw [hbef]; simp
  have hNne : r.input_N ≠ g.initial := by
    intro heq; rw [heq] at hNmem; exact hS hNmem
  -- Hence `r` is not the `S → ε` rule, so it is non-contracting.
  have hnotε : ¬ initial_epsilon_rule g r := by
    rintro ⟨_, hN, _, _⟩; exact hNne hN
  have hnc : grule_noncontracting r := (hg.1 r hr).resolve_left hnotε
  -- The output of `r` is `S`-free by `initial_not_on_rhs`.
  have hout : symbol.nonterminal g.initial ∉ r.output_string := hrhs r hr
  refine ⟨⟨r, mem_gFilter_rules.mpr ⟨hr, hnc⟩, u, v, hbef, haft⟩, ?_⟩
  -- `β = u ++ out ++ v`; `u, v` are sublists of `α` (`S`-free) and `out` is `S`-free.
  rw [haft]
  simp only [List.mem_append, not_or]
  refine ⟨⟨?_, hout⟩, ?_⟩
  · intro hu; exact hS (by rw [hbef]; simp [hu])
  · intro hv; exact hS (by rw [hbef]; simp [hv])

/-- Propagation of the `S`-free invariant across a whole `g`-derivation: from an `S`-free
start, the entire derivation is a `gFilter g`-derivation and the endpoint is `S`-free. -/
private lemma sFree_derives (g : grammar T) (hg : grammar_context_sensitive g)
    (hrhs : initial_not_on_rhs g) {α β : List (symbol T g.nt)}
    (hS : symbol.nonterminal g.initial ∉ α)
    (h : grammar_derives g α β) :
    grammar_derives (gFilter g) α β ∧ symbol.nonterminal g.initial ∉ β := by
  induction h with
  | refl => exact ⟨grammar_deri_self, hS⟩
  | @tail b c _ hstep ih =>
      obtain ⟨hderi, hSb⟩ := ih
      obtain ⟨hstep', hSc⟩ := sFree_step g hg hrhs hSb hstep
      exact ⟨grammar_deri_of_deri_tran hderi hstep', hSc⟩

/-- A transform starting from the single start symbol `[S]` uses a rule with empty context
and `input_N = S`, and the new sentential form is exactly that rule's output. -/
private lemma transforms_initial {g : grammar T} {β : List (symbol T g.nt)}
    (h : grammar_transforms g [symbol.nonterminal g.initial] β) :
    ∃ r ∈ g.rules, r.input_L = [] ∧ r.input_N = g.initial ∧ r.input_R = [] ∧
      β = r.output_string := by
  obtain ⟨r, hr, u, v, hbef, haft⟩ := h
  obtain ⟨rL, rN, rR, rO⟩ := r
  simp only at hr hbef haft
  -- `[S] = u ++ inL ++ [N] ++ inR ++ v`; matching a singleton forces all pieces empty.
  have hlen : (u ++ rL ++ [symbol.nonterminal rN] ++ rR ++ v).length = 1 := by
    rw [← hbef]; rfl
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
  have hL : rL = [] := List.length_eq_zero_iff.mp (by omega)
  have hR : rR = [] := List.length_eq_zero_iff.mp (by omega)
  have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
  subst hu hL hR hv
  simp only [List.nil_append, List.append_nil] at hbef haft
  -- `hbef : [S] = [nonterminal rN]`, so `rN = S`.
  have hN : rN = g.initial := by
    have h1 : (symbol.nonterminal rN : symbol T g.nt) = symbol.nonterminal g.initial := by
      have := hbef.symm
      simpa using this
    exact symbol.nonterminal.inj h1
  refine ⟨⟨[], rN, [], rO⟩, hr, rfl, hN, rfl, ?_⟩
  simpa using haft

/-- Nothing transforms the empty sentential form. -/
private lemma not_transforms_nil {g : grammar T} {β : List (symbol T g.nt)} :
    ¬ grammar_transforms g [] β := by
  rintro ⟨r, _, u, v, hbef, _⟩
  have : (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v).length = 0 := by
    rw [← hbef]; rfl
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- A `g`-derivation out of `[]` lands back on `[]`. -/
private lemma derives_nil_eq {g : grammar T} {β : List (symbol T g.nt)}
    (h : grammar_derives g [] β) : β = [] := by
  rcases grammar_tran_or_id_of_deri h with rfl | ⟨γ, hstep, _⟩
  · rfl
  · exact absurd hstep not_transforms_nil

/-! ## The key language identity -/

/-- **Key lemma.** `gFilter g` generates exactly `L(g)` minus the empty word. -/
private lemma gFilter_language (g : grammar T) (hg : grammar_context_sensitive g) :
    grammar_language (gFilter g) = grammar_language g \ {[]} := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: `gFilter`-derivations are `g`-derivations, and `[] ∉ L(gFilter g)`.
    rintro w hw
    have hwg : grammar_generates g w :=
      gFilter_derives g (by simpa [grammar_generates] using hw)
    refine ⟨hwg, ?_⟩
    rw [Set.mem_singleton_iff]
    rintro rfl
    -- `[] ∉ L(gFilter g)` because `gFilter g` is non-contracting.
    have hd : grammar_derives (gFilter g) [symbol.nonterminal (gFilter g).initial] [] := by
      simpa [grammar_generates] using hw
    have hlen := nc_derives_length_le (gFilter_noncontracting g) hd
    simp at hlen
  · -- `⊇`: take `w ∈ L(g)`, `w ≠ []`, show `w ∈ L(gFilter g)`.
    rintro w ⟨hw, hw0⟩
    have hwne : w ≠ [] := fun h => hw0 (by rw [Set.mem_singleton_iff, h])
    have hwne' : (w.map (symbol.terminal (N := g.nt))) ≠ [] := by
      simpa using hwne
    have hd : grammar_derives g [symbol.nonterminal g.initial] (w.map symbol.terminal) := hw
    -- Split on whether the grammar even has an `S → ε` rule.
    by_cases hε : ∃ r' ∈ g.rules, initial_epsilon_rule g r'
    · -- ε-rule present ⟹ `initial_not_on_rhs g`. Decompose at the first step.
      have hrhs : initial_not_on_rhs g := hg.2 hε
      rcases grammar_tran_or_id_of_deri hd with hbad | ⟨β, hstep, hrest⟩
      · -- `[S] = w.map terminal`: impossible, the start symbol is not a terminal.
        have hmem : symbol.nonterminal g.initial ∈ w.map (symbol.terminal (N := g.nt)) := by
          rw [← hbad]; simp
        rw [List.mem_map] at hmem
        obtain ⟨a, _, ha⟩ := hmem
        exact absurd ha (by simp)
      -- First step: empty context, `input_N = S`, `β = out`.
      obtain ⟨r, hr, hrL, hN, hrR, hβ⟩ := transforms_initial hstep
      -- `r` is not the `S → ε` rule (otherwise `β = []` is stuck, contradicting `w ≠ []`).
      have hrnotε : ¬ initial_epsilon_rule g r := by
        rintro ⟨_, _, _, hO⟩
        rw [hO] at hβ; subst hβ
        exact hwne' (derives_nil_eq hrest)
      have hSβ : symbol.nonterminal g.initial ∉ β := by rw [hβ]; exact hrhs r hr
      have hnc : grule_noncontracting r := (hg.1 r hr).resolve_left hrnotε
      have hstep' : grammar_transforms (gFilter g) [symbol.nonterminal g.initial] β := by
        refine ⟨r, mem_gFilter_rules.mpr ⟨hr, hnc⟩, [], [], ?_, ?_⟩
        · simp [hN, hrL, hrR]
        · simpa using hβ
      have hrest' := (sFree_derives g hg hrhs hSβ hrest).1
      exact grammar_deri_of_tran_deri hstep' hrest'
    · -- No `S → ε` rule ⟹ every rule is non-contracting ⟹ `gFilter g` keeps all rules.
      have hall : ∀ r' ∈ g.rules, grule_noncontracting r' := fun r' hr' =>
        (hg.1 r' hr').resolve_left (fun hεr' => hε ⟨r', hr', hεr'⟩)
      exact gFilter_derives_of_allNC g hall hd

/-! ## ε-elimination -/

/-- **ε-elimination.** Every broadly-context-sensitive grammar admits an equivalent (off the
empty word) ε-free **non-contracting** grammar with finitely many nonterminals. We take
`gFilter g` (delete the contracting rules) and finitize its nonterminals with
`restrictGrammar`. -/
public theorem exists_noncontracting_offEmpty_of_CS (g : grammar T)
    (hg : grammar_context_sensitive g) :
    ∃ g₀ : grammar T, Finite g₀.nt ∧ grammar_noncontracting g₀ ∧
      grammar_language g₀ = grammar_language g \ {[]} := by
  obtain ⟨g₀, hfin, hnc, hlang⟩ :=
    noncontracting_equivalent_finiteNT (gFilter g) (gFilter_noncontracting g)
  exact ⟨g₀, hfin, hnc, by rw [hlang]; exact gFilter_language g hg⟩
