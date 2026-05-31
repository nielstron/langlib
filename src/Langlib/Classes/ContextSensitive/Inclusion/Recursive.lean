module

public import Langlib.Classes.ContextSensitive.Decidability.Computability
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Closure.Intersection
public import Langlib.Classes.RecursivelyEnumerable.Closure.Union
public import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Complement
public import Langlib.Grammars.Unrestricted.FiniteNonterminals
public import Langlib.Grammars.ContextSensitive.Basic.FiniteNT
public import Langlib.Classes.RecursivelyEnumerable.Examples.EmptyWord
public import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive
public import Langlib.Grammars.Unrestricted.Toolbox
import Mathlib.Tactic
@[expose]
public section



/-! # Context-Sensitive Languages are Recursive

This file proves the bridge theorem that every context-sensitive language (in the
broad `S → ε`-optional `grammar_context_sensitive` sense) is recursive, and the
corresponding class-level inclusion `(CS : Set (Language T)) ⊆ Recursive`.

## Strategy

Given `is_CS L` we get an unrestricted grammar `g` with `grammar_context_sensitive g`
and `grammar_language g = L`. Then:

* `is_RE L` is immediate via `is_RE_of_CS`.
* `is_RE Lᶜ` is the work. We produce a **non-contracting** grammar `g₀` with finitely
  many nonterminals generating `L \ {[]}` (this is ε-elimination of the optional start
  rule `S → ε`, isolated as `exists_noncontracting_offEmpty_of_CS`). Its complement is
  RE by `is_RE_compl_of_noncontracting`. Then `Lᶜ` differs from `(grammar_language g₀)ᶜ`
  only at the single word `[]`, and RE-ness is preserved under intersection with the
  regular language `{[]}ᶜ`, giving `is_RE Lᶜ`.
* Post's theorem `is_Recursive_of_isRE_of_isRE_compl` concludes.

## Main declarations

* `is_Recursive_of_is_CS`
* `CS_subset_Recursive_class`
-/

open Relation

variable {T : Type}

/-! ## ε-elimination of the optional start rule

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
`g'`. So the whole `g`-derivation is in fact a `g'`-derivation. -/

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

/-! ## RE-ness of the complement

The complement of a non-contracting language is RE (`is_RE_compl_of_noncontracting`).
We package the finite-nonterminal instance plumbing, then adjust at the single word
`[]`. -/

/-- The complement of a finite-nonterminal non-contracting language is RE. -/
public theorem is_RE_compl_of_noncontracting_finite
    [Fintype T] [DecidableEq T] [Primcodable T]
    (g₀ : grammar T) (hfin : Finite g₀.nt) (hnc : grammar_noncontracting g₀) :
    is_RE (grammar_language g₀)ᶜ := by
  haveI : Fintype g₀.nt := Fintype.ofFinite _
  haveI : DecidableEq g₀.nt := Classical.decEq _
  haveI : Primcodable g₀.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g₀.nt)) (Fintype.truncEquivFin g₀.nt).out
  exact is_RE_compl_of_noncontracting g₀ hnc

/-- If `M` agrees with `L` off the empty word (`M = L \ {[]}`), and `Mᶜ` is RE, then
`Lᶜ` is RE.

`Lᶜ` decomposes as `(Mᶜ ⊓ {[]}ᶜ) + (Lᶜ ⊓ {[]})`: off the empty word `L` and `M` agree,
and the single word `[]` is added back exactly when `[] ∉ L`. The first part is an
intersection of RE languages; the second is either `{[]}` or `∅`, both RE; RE is closed
under union. -/
public theorem is_RE_compl_of_compl_offEmpty
    [Fintype T] [DecidableEq T] [Primcodable T]
    {L M : Language T} (hM : M = L \ {[]}) (hcompl : is_RE Mᶜ) :
    is_RE Lᶜ := by
  -- The "off-empty" part.
  have hoff : is_RE (Mᶜ ⊓ ({[]} : Language T)ᶜ) :=
    RE_of_RE_i_RE Mᶜ (({[]} : Language T)ᶜ) ⟨hcompl, emptyWordLanguage_compl_isRE⟩
  -- The "at-empty" part: either `{[]}` or `∅`.
  have hat : is_RE (Lᶜ ⊓ ({[]} : Language T)) := by
    by_cases h0 : [] ∈ L
    · have : Lᶜ ⊓ ({[]} : Language T) = (⊥ : Language T) := by
        ext w
        constructor
        · rintro ⟨hwL, (rfl : w = [])⟩; exact (hwL h0).elim
        · intro hw
          rw [Set.bot_eq_empty, Set.mem_empty_iff_false] at hw
          exact hw.elim
      rw [this]; exact is_RE_empty
    · have : Lᶜ ⊓ ({[]} : Language T) = ({[]} : Language T) := by
        ext w; constructor
        · rintro ⟨_, hw⟩; exact hw
        · rintro (rfl : w = []); exact ⟨h0, rfl⟩
      rw [this]; exact emptyWordLanguage_isRE
  -- Assemble: `Lᶜ = (Mᶜ ⊓ {[]}ᶜ) + (Lᶜ ⊓ {[]})`.
  have heq : Lᶜ = (Mᶜ ⊓ ({[]} : Language T)ᶜ) + (Lᶜ ⊓ ({[]} : Language T)) := by
    subst hM
    ext w
    rw [Language.mem_add]
    constructor
    · intro hwL
      -- `hwL : w ∉ L`
      by_cases hw0 : w = []
      · exact Or.inr ⟨hwL, hw0⟩
      · refine Or.inl ⟨?_, ?_⟩
        · -- `w ∉ L \ {[]}`
          rintro ⟨hwL', _⟩; exact hwL hwL'
        · -- `w ∉ {[]}`
          exact hw0
    · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
      · -- `h1 : w ∉ L \ {[]}`, `h2 : w ∉ {[]}` ⊢ `w ∉ L`
        intro hwL'
        exact h1 ⟨hwL', fun (hw0 : w = []) => h2 hw0⟩
      · -- `h1 : w ∉ L`
        exact h1
  rw [heq]
  exact RE_of_RE_u_RE _ _ ⟨hoff, hat⟩

/-! ## Main bridge theorems -/

/-- **Every context-sensitive language is recursive.** -/
public theorem is_Recursive_of_is_CS
    [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (h : is_CS L) : is_Recursive L := by
  obtain ⟨g, hgcs, hgL⟩ := h
  -- `L` is RE.
  have hRE : is_RE L := is_RE_of_CS ⟨g, hgcs, hgL⟩
  -- `Lᶜ` is RE via the ε-eliminated non-contracting grammar.
  obtain ⟨g₀, hfin, hnc, hg₀⟩ := exists_noncontracting_offEmpty_of_CS g hgcs
  have hMcompl : is_RE (grammar_language g₀)ᶜ :=
    is_RE_compl_of_noncontracting_finite g₀ hfin hnc
  have hg₀L : grammar_language g₀ = L \ {[]} := by rw [hg₀, hgL]
  have hREc : is_RE Lᶜ := is_RE_compl_of_compl_offEmpty hg₀L hMcompl
  exact is_Recursive_of_isRE_of_isRE_compl hRE hREc

/-- **The class of context-sensitive languages is a subset of the recursive languages.** -/
public theorem CS_subset_Recursive_class
    [Fintype T] [DecidableEq T] [Primcodable T] :
    (CS : Set (Language T)) ⊆ (Recursive : Set (Language T)) := by
  intro L hL
  exact is_Recursive_of_is_CS hL
