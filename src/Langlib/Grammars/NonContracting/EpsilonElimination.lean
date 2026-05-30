module

public import Langlib.Grammars.Unrestricted.Toolbox
public import Langlib.Classes.ContextSensitive.Definition
import Mathlib.Tactic
@[expose]
public section

/-! # ε-elimination for loosely-context-sensitive grammars

A `grammar_context_sensitive` grammar `g` has at most one erasing rule, the optional
`S → ε` rule (`initial_epsilon_rule`), where `S = g.initial`; every other rule is
non-contracting. This file builds a genuinely **non-contracting** grammar `g_elim g`
with `grammar_language (g_elim g) = grammar_language g \ {[]}` (modulo the completeness
direction, see `EpsilonElimination` blockers below).

## Strategy (classical nullable elimination, RHS variant)

* A nonterminal/word is *nullable* if it derives `[]` in `g`.
* `NullableRelated u v` (our analogue of the context-free notion) holds when `v` can be
  obtained from `u` by inserting nullable nonterminals; equivalently `g` derives `v →* u`
  by erasing those nullable nonterminals.
* `g_elim g` keeps every non-contracting rule of `g` and, for each such rule
  `inL A inR → out`, adds every variant `inL A inR → out'` where `NullableRelated out' out`,
  `out'` is non-empty, and the variant is still non-contracting. The `S → ε` rule is dropped.

This file fully proves: the construction is non-contracting, and **soundness**
(`grammar_language (g_elim g) ⊆ grammar_language g \ {[]}`). Completeness is isolated.
-/

open Relation

variable {T : Type}

namespace EpsElim

/-! ## Nullable words and `NullableRelated` -/

/-- A word is nullable if `g` derives it to the empty string. -/
@[expose]
def NullableWord (g : grammar T) (u : List (symbol T g.nt)) : Prop :=
  grammar_derives g u []

/-- A nonterminal is nullable if `g` derives `[n]` to the empty string. -/
@[expose]
def Nullable (g : grammar T) (n : g.nt) : Prop :=
  grammar_derives g [symbol.nonterminal n] []

/-- `NullableRelated g u v`: `v` reduces to `u` by erasing some interspersed nullable
nonterminals (so `u` is the "shorter" word). Mirrors the context-free `NullableRelated`. -/
inductive NullableRelated (g : grammar T) :
    List (symbol T g.nt) → List (symbol T g.nt) → Prop where
  | nil : NullableRelated g [] []
  | cons_match {u v : List (symbol T g.nt)} (huv : NullableRelated g u v) (s : symbol T g.nt) :
      NullableRelated g (s :: u) (s :: v)
  | cons_nterm_nullable {u v : List (symbol T g.nt)} (huv : NullableRelated g u v) {n : g.nt}
      (hn : Nullable g n) : NullableRelated g u (symbol.nonterminal n :: v)

/-- `NullableRelated` is reflexive. -/
@[refl]
lemma NullableRelated.refl (g : grammar T) (u : List (symbol T g.nt)) :
    NullableRelated g u u := by
  induction u with
  | nil => exact .nil
  | cons d _ ih => exact .cons_match ih d

/-- The defining property: if `NullableRelated g u v` then `g` derives `v →* u`. -/
lemma NullableRelated.derives {g : grammar T} {u v : List (symbol T g.nt)}
    (huv : NullableRelated g u v) : grammar_derives g v u := by
  induction huv with
  | nil => exact grammar_deri_self
  | @cons_match u v huv s ih =>
      have := grammar_deri_with_prefix (g := g) [s] ih
      simpa using this
  | @cons_nterm_nullable u v huv n hn ih =>
      -- `n :: v →* v` (erase the nullable head) then `v →* u`.
      have h1 : grammar_derives g (symbol.nonterminal n :: v) ([] ++ v) := by
        have := grammar_deri_with_postfix (g := g) v hn
        simpa using this
      exact grammar_deri_of_deri_deri (by simpa using h1) ih

/-- `NullableRelated` is closed under append. -/
lemma NullableRelated.append {g : grammar T} {u₁ u₂ v₁ v₂ : List (symbol T g.nt)}
    (h₁ : NullableRelated g u₁ v₁) (h₂ : NullableRelated g u₂ v₂) :
    NullableRelated g (u₁ ++ u₂) (v₁ ++ v₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons_match huv s ih => exact NullableRelated.cons_match ih s
  | cons_nterm_nullable huv hn ih => exact NullableRelated.cons_nterm_nullable ih hn

/-! ## Enumerating nullable variants of an output -/

open Classical in
/-- All words obtainable from `out` by deleting some individually-nullable nonterminals.
The classical decidability instance is used purely to filter; the result is a genuine list. -/
noncomputable def nullableVariants (g : grammar T) :
    List (symbol T g.nt) → List (List (symbol T g.nt))
  | [] => [[]]
  | s :: rest =>
      let tails := nullableVariants g rest
      (tails.map (s :: ·)) ++
        (match s with
         | symbol.nonterminal n => if Nullable g n then tails else []
         | symbol.terminal _ => [])

open Classical in
/-- Membership in `nullableVariants` is exactly `NullableRelated`. -/
lemma mem_nullableVariants_iff {g : grammar T} {out out' : List (symbol T g.nt)} :
    out' ∈ nullableVariants g out ↔ NullableRelated g out' out := by
  induction out generalizing out' with
  | nil =>
      simp only [nullableVariants, List.mem_singleton]
      constructor
      · rintro rfl; exact .nil
      · intro h; cases h; rfl
  | cons s rest ih =>
      simp only [nullableVariants, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨t, ht, rfl⟩ | hdrop)
        · exact NullableRelated.cons_match (ih.mp ht) s
        · rcases s with t | n
          · simp only [List.not_mem_nil] at hdrop
          · by_cases hn : Nullable g n
            · simp only [hn, if_true] at hdrop
              exact NullableRelated.cons_nterm_nullable (ih.mp hdrop) hn
            · simp only [hn, if_false, List.not_mem_nil] at hdrop
      · intro h
        cases h with
        | @cons_match u v huv s => exact Or.inl ⟨u, ih.mpr huv, rfl⟩
        | @cons_nterm_nullable u v huv n hn =>
            refine Or.inr ?_
            simp only [hn, if_true]
            exact ih.mpr huv

/-! ## The ε-eliminated grammar -/

open Classical in
/-- Variant rules of a single rule `r`: keep its context `inL A inR`, replace the output by
any nullable variant that is still non-contracting. -/
noncomputable def elimRulesOf (g : grammar T) (r : grule T g.nt) : List (grule T g.nt) :=
  (nullableVariants g r.output_string).filterMap (fun out' =>
    if r.input_L.length + 1 + r.input_R.length ≤ out'.length then
      some { input_L := r.input_L, input_N := r.input_N,
             input_R := r.input_R, output_string := out' }
    else none)

open Classical in
/-- The ε-eliminated grammar: drop the `S → ε` rule, replace every non-contracting rule by all
its non-contracting nullable variants. Same nonterminals and start symbol as `g`. -/
noncomputable def g_elim (g : grammar T) : grammar T where
  nt := g.nt
  initial := g.initial
  rules := (g.rules.filter (fun r => ¬ initial_epsilon_rule g r)).flatMap (elimRulesOf g)

@[simp] lemma g_elim_nt (g : grammar T) : (g_elim g).nt = g.nt := rfl
@[simp] lemma g_elim_initial (g : grammar T) : (g_elim g).initial = g.initial := rfl

open Classical in
/-- Characterization of the rules of `elimRulesOf`. -/
lemma mem_elimRulesOf {g : grammar T} {r r' : grule T g.nt} :
    r' ∈ elimRulesOf g r ↔
      r'.input_L = r.input_L ∧ r'.input_N = r.input_N ∧ r'.input_R = r.input_R ∧
      NullableRelated g r'.output_string r.output_string ∧
      r.input_L.length + 1 + r.input_R.length ≤ r'.output_string.length := by
  unfold elimRulesOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨out', hout', hsome⟩
    by_cases hlen : r.input_L.length + 1 + r.input_R.length ≤ out'.length
    · simp only [hlen, if_true, Option.some.injEq] at hsome
      subst hsome
      exact ⟨rfl, rfl, rfl, mem_nullableVariants_iff.mp hout', hlen⟩
    · rw [if_neg hlen] at hsome; exact absurd hsome (by simp)
  · rintro ⟨hL, hN, hR, hrel, hlen⟩
    obtain ⟨L', N', R', O'⟩ := r'
    simp only at hL hN hR hrel hlen
    subst hL; subst hN; subst hR
    refine ⟨O', mem_nullableVariants_iff.mpr hrel, ?_⟩
    simp only [hlen, if_true, Option.some.injEq]

open Classical in
/-- Characterization of the rules of `g_elim g`. -/
lemma mem_g_elim_rules {g : grammar T} {r' : grule T g.nt} :
    r' ∈ (g_elim g).rules ↔
      ∃ r ∈ g.rules, ¬ initial_epsilon_rule g r ∧ r' ∈ elimRulesOf g r := by
  show r' ∈ (g.rules.filter _).flatMap (elimRulesOf g) ↔ _
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hr'⟩
    rw [List.mem_filter] at hr
    exact ⟨r, hr.1, by simpa using hr.2, hr'⟩
  · rintro ⟨r, hr, hne, hr'⟩
    exact ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hne⟩, hr'⟩

/-- The ε-eliminated grammar is non-contracting. -/
theorem g_elim_noncontracting (g : grammar T) : grammar_noncontracting (g_elim g) := by
  intro r' hr'
  rw [mem_g_elim_rules] at hr'
  obtain ⟨r, hr, hne, hr'elim⟩ := hr'
  rw [mem_elimRulesOf] at hr'elim
  obtain ⟨hL, hN, hR, hrel, hlen⟩ := hr'elim
  show r'.output_string.length ≥ r'.input_L.length + 1 + r'.input_R.length
  rw [hL, hR]; exact hlen

/-! ## Soundness: every `g_elim`-derivation is a `g`-derivation -/

/-- A single `g_elim` transform step is realized by a `g`-derivation. -/
lemma g_elim_transform_derives (g : grammar T) {a b : List (symbol T g.nt)}
    (h : grammar_transforms (g_elim g) a b) : grammar_derives g a b := by
  -- View `h` as a `g.nt`-typed transform (`(g_elim g).nt` is defeq `g.nt`).
  obtain ⟨r', hr', u, v, hbef, haft⟩ :
      ∃ (r' : grule T g.nt), r' ∈ (g_elim g).rules ∧ ∃ (u v : List (symbol T g.nt)),
        a = u ++ r'.input_L ++ [symbol.nonterminal r'.input_N] ++ r'.input_R ++ v ∧
        b = u ++ r'.output_string ++ v := by
    obtain ⟨r', hr', u, v, hbef, haft⟩ := h
    exact ⟨r', hr', u, v, hbef, haft⟩
  rw [mem_g_elim_rules] at hr'
  obtain ⟨r, hr, hne, hr'elim⟩ := hr'
  rw [mem_elimRulesOf] at hr'elim
  obtain ⟨hL, hN, hR, hrel, hlen⟩ := hr'elim
  -- The original rule fires: `u ++ inL ++ [N] ++ inR ++ v → u ++ out ++ v`.
  have hstep : grammar_transforms g a (u ++ r.output_string ++ v) := by
    refine ⟨r, hr, u, v, ?_, rfl⟩
    rw [hbef, hL, hN, hR]
  -- Then `out →* out'`, so `u ++ out ++ v →* u ++ out' ++ v`.
  have hmid : grammar_derives g (u ++ r.output_string ++ v) b := by
    rw [haft]
    have hcore : grammar_derives g r.output_string r'.output_string := hrel.derives
    have := grammar_deri_with_prefix (g := g) u
      (grammar_deri_with_postfix (g := g) v hcore)
    simpa [List.append_assoc] using this
  exact grammar_deri_of_tran_deri hstep hmid

/-- Soundness on derivations: every `g_elim`-derivation is a `g`-derivation. -/
lemma g_elim_derives_derives (g : grammar T) {a b : List (symbol T g.nt)}
    (h : grammar_derives (g_elim g) a b) : grammar_derives g a b := by
  induction h with
  | refl => exact grammar_deri_self
  | tail _ hstep ih => exact grammar_deri_of_deri_deri ih (g_elim_transform_derives g hstep)

/-- Soundness on words: every word generated by `g_elim g` is generated by `g`. -/
lemma g_elim_generates (g : grammar T) {w : List T}
    (hw : grammar_generates (g_elim g) w) : grammar_generates g w := by
  have := g_elim_derives_derives g (a := [symbol.nonterminal (g_elim g).initial])
    (b := w.map symbol.terminal) hw
  simpa [grammar_generates] using this

/-! ## A non-contracting grammar never generates the empty word -/

/-- A single non-contracting transform step does not decrease length. -/
lemma noncontracting_step_len {g : grammar T} (hnc : grammar_noncontracting g)
    {a b : List (symbol T g.nt)} (h : grammar_transforms g a b) : a.length ≤ b.length := by
  obtain ⟨r, hr, u, v, rfl, rfl⟩ := h
  have := hnc r hr
  simp only [grule_noncontracting] at this
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- A non-contracting derivation does not decrease length. -/
lemma noncontracting_derives_len {g : grammar T} (hnc : grammar_noncontracting g)
    {a b : List (symbol T g.nt)} (h : grammar_derives g a b) : a.length ≤ b.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (noncontracting_step_len hnc hstep)

/-- A non-contracting grammar does not generate the empty word. -/
lemma noncontracting_not_generates_nil {g : grammar T} (hnc : grammar_noncontracting g) :
    ¬ grammar_generates g [] := by
  intro h
  have := noncontracting_derives_len hnc h
  simp at this

/-! ## Completeness (the remaining classical gap)

This is the hard direction of ε-elimination. See the file header and the report for why the
per-symbol `NullableRelated` developed above is *insufficient* for the context-sensitive
case: when the output of a rule fully reduces to `[]`, the matched input context
`inL ++ [N] ++ inR` must be absorbed as a *word*-level nullable block, which need not be
symbol-wise nullable (counterexample: rules `A B → S S`, `S → ε` make `[A,B]` nullable as a
word though neither `A` nor `B` is individually nullable). A faithful completeness proof
requires the full word-level nullable-relation together with a construction that may delete
nullable *input-context*; this is the genuine context-sensitive ε-elimination and remains to
be formalized. -/

/-- **Completeness of ε-elimination (REMAINING GAP).** Every non-empty word generated by
`g` is generated by `g_elim g`. -/
theorem g_elim_complete (g : grammar T) (hg : grammar_context_sensitive g)
    {w : List T} (hwne : w ≠ []) (hw : grammar_generates g w) :
    grammar_generates (g_elim g) w := by
  sorry

/-- The language of `g_elim g` is exactly `L(g) \ {[]}` for a (loosely) context-sensitive `g`. -/
theorem g_elim_language (g : grammar T) (hg : grammar_context_sensitive g) :
    grammar_language (g_elim g) = grammar_language g \ {[]} := by
  apply Set.eq_of_subset_of_subset
  · intro w hw
    refine ⟨g_elim_generates g hw, ?_⟩
    intro hw0
    rw [Set.mem_singleton_iff] at hw0
    subst hw0
    exact noncontracting_not_generates_nil (g_elim_noncontracting g) hw
  · rintro w ⟨hw, hw0⟩
    have hwne : w ≠ [] := by
      intro h; exact hw0 (by rw [h]; rfl)
    exact g_elim_complete g hg hwne hw

end EpsElim
