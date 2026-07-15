module

public import Langlib.Grammars.ContextFree.Definition

/-!
# LR(k) Grammars

This file defines the grammar-side deterministic context-free notion used in
parser theory, as a restriction of the repository's own context-free grammars
(`CF_grammar`).  The key definition is `CF_grammar.IsLRk`: after a rightmost
derivation step, the reducible handle is uniquely determined by the already-built
sentential prefix and by `k` terminal lookahead symbols.

The definition uses the standard fresh-start augmentation.  This matters even
for language recognition: the completed augmented start rule is the parser's
accept action, so including it in handle uniqueness rules out accept/reduce and
accept/shift conflicts as well as ordinary reduce/reduce and shift/reduce
conflicts.

This is the grammar-side class matching DPDAs.  The equivalence is proved by
the two standard constructions in `Langlib.Grammars.LR.Equivalence`:

* an LR(k) parser as a DPDA, proving `is_LR → is_DCF`;
* a deterministic grammar construction from a DPDA, proving `is_DCF → is_LR`.

A context-free rule is, in this development, a pair `r : g.nt × List (symbol T g.nt)`
whose first component `r.1` is the left-hand nonterminal and whose second component
`r.2` is the right-hand output string.
-/

open Language

namespace CF_grammar

variable {T : Type}

/-- A rightmost use of a context-free rule `r = (input, output)`.

The rule rewrites an occurrence of `r.1` whose suffix contains terminals only. -/
@[expose]
public def RewritesRightmost {N : Type} (r : N × List (symbol T N))
    (u v : List (symbol T N)) : Prop :=
  ∃ (p : List (symbol T N)) (lookahead : List T),
    u = p ++ [symbol.nonterminal r.1] ++ lookahead.map symbol.terminal ∧
      v = p ++ r.2 ++ lookahead.map symbol.terminal

variable (g : CF_grammar T)

/-- A single rightmost derivation step in a context-free grammar. -/
@[expose]
public def ProducesRightmost (u v : List (symbol T g.nt)) : Prop :=
  ∃ r ∈ g.rules, RewritesRightmost r u v

/-- Rightmost derivation: reflexive-transitive closure of rightmost production. -/
@[expose]
public abbrev DerivesRightmost :
    List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.ProducesRightmost

/-- The `k` terminal symbols visible as LR lookahead. -/
@[expose]
public def lrLookahead (k : ℕ) (w : List T) : List T :=
  w.take k

/-- Embed an original grammar symbol into a grammar with a fresh start
nonterminal.  `none` is reserved for the fresh start and original nonterminals
are embedded with `some`. -/
@[expose]
public def augmentSymbol {N : Type} : symbol T N → symbol T (Option N)
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal A => symbol.nonterminal (some A)

@[simp]
public theorem augmentSymbol_terminal {N : Type} (t : T) :
    augmentSymbol (symbol.terminal (N := N) t) = symbol.terminal t := rfl

@[simp]
public theorem augmentSymbol_nonterminal {N : Type} (A : N) :
    augmentSymbol (symbol.nonterminal (T := T) A) = symbol.nonterminal (some A) := rfl

/-- Embed a sentential form into the fresh-start augmentation. -/
@[expose]
public def augmentString {N : Type} (w : List (symbol T N)) :
    List (symbol T (Option N)) :=
  w.map augmentSymbol

@[simp]
public theorem augmentString_nil {N : Type} :
    augmentString ([] : List (symbol T N)) = [] := rfl

@[simp]
public theorem augmentString_cons {N : Type} (a : symbol T N)
    (w : List (symbol T N)) :
    augmentString (a :: w) = augmentSymbol a :: augmentString w := rfl

/-- Embed a production into the fresh-start augmentation. -/
@[expose]
public def augmentRule {N : Type} (r : N × List (symbol T N)) :
    Option N × List (symbol T (Option N)) :=
  (some r.1, augmentString r.2)

/-- The distinguished production of the augmented grammar. -/
@[expose]
public def augmentStartRule : Option g.nt × List (symbol T (Option g.nt)) :=
  (none, [symbol.nonterminal (some g.initial)])

/-- Fresh-start augmentation of a context-free grammar.

The new initial nonterminal is `none`; every original nonterminal is renamed to
`some A`; and the sole production headed by the fresh start is `none → some S`.
-/
@[expose]
public def augment : CF_grammar T where
  nt := Option g.nt
  initial := none
  rules := augmentStartRule g :: g.rules.map augmentRule

@[simp]
public theorem augment_initial : g.augment.initial = none := rfl

@[simp]
public theorem augment_start_ne_original (A : g.nt) :
    g.augment.initial ≠ some A := by
  simp [augment]

@[simp]
public theorem augmentString_terminal (t : T) :
    augmentString ([symbol.terminal t] : List (symbol T g.nt)) =
      [symbol.terminal t] := rfl

@[simp]
public theorem augmentString_nonterminal (A : g.nt) :
    augmentString ([symbol.nonterminal A] : List (symbol T g.nt)) =
      [symbol.nonterminal (some A)] := rfl

@[simp]
public theorem augmentString_append (u v : List (symbol T g.nt)) :
    augmentString (u ++ v) = augmentString u ++ augmentString v := by
  simp [augmentString]

@[simp]
public theorem augmentString_map_terminal (w : List T) :
    augmentString (N := g.nt) (w.map (symbol.terminal (N := g.nt))) =
      w.map (symbol.terminal (N := Option g.nt)) := by
  induction w with
  | nil => rfl
  | cons t w ih => simp [ih]

@[simp]
public theorem augmentStartRule_mem : augmentStartRule g ∈ g.augment.rules := by
  simp [augment]

public theorem augmentRule_mem {r : g.nt × List (symbol T g.nt)} (hr : r ∈ g.rules) :
    augmentRule r ∈ g.augment.rules := by
  simp only [augment, List.mem_cons, List.mem_map]
  exact Or.inr ⟨r, hr, rfl⟩

/-- Forget the fresh start symbol.  The fresh start itself is sent to the
original initial nonterminal, so the augmented start production projects to a
reflexive step. -/
@[expose]
public def projectAugmentSymbol : symbol T (Option g.nt) → symbol T g.nt
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal none => symbol.nonterminal g.initial
  | symbol.nonterminal (some A) => symbol.nonterminal A

@[simp]
public theorem projectAugmentSymbol_augmentSymbol (a : symbol T g.nt) :
    g.projectAugmentSymbol (augmentSymbol a) = a := by
  cases a <;> rfl

/-- Forget the fresh start symbol in a sentential form. -/
@[expose]
public def projectAugmentString (w : List (symbol T (Option g.nt))) :
    List (symbol T g.nt) :=
  w.map g.projectAugmentSymbol

@[simp]
public theorem projectAugmentString_append (u v : List (symbol T (Option g.nt))) :
    g.projectAugmentString (u ++ v) =
      g.projectAugmentString u ++ g.projectAugmentString v := by
  simp [projectAugmentString]

@[simp]
public theorem projectAugmentString_augmentString (w : List (symbol T g.nt)) :
    g.projectAugmentString (augmentString w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change g.projectAugmentSymbol (augmentSymbol a) ::
        g.projectAugmentString (augmentString w) = a :: w
      rw [g.projectAugmentSymbol_augmentSymbol, ih]

@[simp]
public theorem projectAugmentString_map_terminal (w : List T) :
    g.projectAugmentString
        (w.map (symbol.terminal (N := Option g.nt))) =
      w.map (symbol.terminal (N := g.nt)) := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      change symbol.terminal t ::
        g.projectAugmentString
          (w.map (symbol.terminal (N := Option g.nt))) =
        symbol.terminal t :: w.map (symbol.terminal (N := g.nt))
      rw [ih]

/-- An original rightmost rewrite embeds as a rightmost rewrite of the
augmented grammar. -/
public theorem RewritesRightmost.augment
    {r : g.nt × List (symbol T g.nt)} {u v : List (symbol T g.nt)}
    (h : RewritesRightmost r u v) :
    RewritesRightmost (augmentRule r) (augmentString u) (augmentString v) := by
  rcases h with ⟨p, s, hu, hv⟩
  refine ⟨augmentString p, s, ?_, ?_⟩
  · rw [hu]
    simp [augmentRule, augmentString_append]
  · rw [hv]
    simp [augmentRule, augmentString_append]

/-- An original rightmost production step embeds into the augmented grammar. -/
public theorem ProducesRightmost.augment
    {u v : List (symbol T g.nt)} (h : g.ProducesRightmost u v) :
    g.augment.ProducesRightmost (augmentString u) (augmentString v) := by
  rcases h with ⟨r, hr, hrewrite⟩
  exact ⟨augmentRule r, augmentRule_mem g hr, hrewrite.augment⟩

/-- An original rightmost derivation embeds into the augmented grammar, starting
at the embedded original start symbol. -/
public theorem DerivesRightmost.augment
    {u v : List (symbol T g.nt)} (h : g.DerivesRightmost u v) :
    g.augment.DerivesRightmost (augmentString u) (augmentString v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.augment

/-- The distinguished start production is a rightmost step. -/
public theorem augment_start_producesRightmost :
    g.augment.ProducesRightmost
      [symbol.nonterminal g.augment.initial]
      [symbol.nonterminal (some g.initial)] := by
  refine ⟨augmentStartRule g, augmentStartRule_mem g, [], [], ?_, ?_⟩ <;>
    simp [augment, augmentStartRule]

/-- Lift an original rightmost derivation from its start symbol to a derivation
from the fresh augmented start symbol. -/
public theorem augment_derivesRightmost
    {v : List (symbol T g.nt)}
    (h : g.DerivesRightmost [symbol.nonterminal g.initial] v) :
    g.augment.DerivesRightmost
      [symbol.nonterminal g.augment.initial] (augmentString v) := by
  exact (Relation.ReflTransGen.single (augment_start_producesRightmost g)).trans h.augment

/-- An ordinary context-free rewrite embeds into the augmented grammar. -/
public theorem transforms_augment
    {u v : List (symbol T g.nt)} (h : CF_transforms g u v) :
    CF_transforms g.augment (augmentString u) (augmentString v) := by
  rcases h with ⟨r, p, q, hr, hu, hv⟩
  refine ⟨augmentRule r, augmentString p, augmentString q,
    augmentRule_mem g hr, ?_, ?_⟩
  · rw [hu]
    simp [augmentRule, augmentString_append]
  · rw [hv]
    simp [augmentRule, augmentString_append]

/-- An ordinary derivation embeds into the augmented grammar. -/
public theorem derives_augment
    {u v : List (symbol T g.nt)} (h : CF_derives g u v) :
    CF_derives g.augment (augmentString u) (augmentString v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (transforms_augment g hstep)

/-- The distinguished start production is an ordinary context-free step. -/
public theorem augment_start_transforms :
    CF_transforms g.augment
      [symbol.nonterminal g.augment.initial]
      [symbol.nonterminal (some g.initial)] := by
  refine ⟨augmentStartRule g, [], [], augmentStartRule_mem g, ?_, ?_⟩ <;>
    simp [augment, augmentStartRule]

/-- Lift an original derivation from its start symbol to a derivation from the
fresh augmented start symbol. -/
public theorem augment_derives
    {v : List (symbol T g.nt)}
    (h : CF_derives g [symbol.nonterminal g.initial] v) :
    CF_derives g.augment
      [symbol.nonterminal g.augment.initial] (augmentString v) := by
  exact (Relation.ReflTransGen.single (augment_start_transforms g)).trans
    (derives_augment g h)

/-- Projecting one augmented context-free step gives zero or one original
steps.  The zero-step case is exactly the fresh start production. -/
public theorem derives_project_augment_of_transforms
    {u v : List (symbol T (Option g.nt))}
    (h : CF_transforms g.augment u v) :
    CF_derives g (g.projectAugmentString u) (g.projectAugmentString v) := by
  rcases h with ⟨r, p, q, hr, hu, hv⟩
  rcases List.mem_cons.mp hr with hstart | hmapped
  · subst r
    rw [hu, hv]
    simpa [augmentStartRule, projectAugmentString, projectAugmentSymbol,
      List.map_append] using
      (Relation.ReflTransGen.refl :
        CF_derives g
          (g.projectAugmentString p ++ [symbol.nonterminal g.initial] ++
            g.projectAugmentString q)
          (g.projectAugmentString p ++ [symbol.nonterminal g.initial] ++
            g.projectAugmentString q))
  · rcases List.mem_map.mp hmapped with ⟨r₀, hr₀, heq⟩
    subst r
    apply Relation.ReflTransGen.single
    refine ⟨r₀, g.projectAugmentString p, g.projectAugmentString q, hr₀, ?_, ?_⟩
    · rw [hu]
      simp [augmentRule, projectAugmentString, projectAugmentSymbol]
    · rw [hv]
      simp only [g.projectAugmentString_append]
      have hright : g.projectAugmentString (augmentRule r₀).2 = r₀.2 := by
        exact g.projectAugmentString_augmentString r₀.2
      rw [hright]

/-- Project an augmented derivation back to the original grammar. -/
public theorem derives_project_augment
    {u v : List (symbol T (Option g.nt))}
    (h : CF_derives g.augment u v) :
    CF_derives g (g.projectAugmentString u) (g.projectAugmentString v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.trans (derives_project_augment_of_transforms g hstep)

/-- Projecting one augmented rightmost step gives zero or one original
rightmost steps.  Again, the zero-step case is the fresh start production. -/
public theorem derivesRightmost_project_augment_of_produces
    {u v : List (symbol T (Option g.nt))}
    (h : g.augment.ProducesRightmost u v) :
    g.DerivesRightmost (g.projectAugmentString u) (g.projectAugmentString v) := by
  rcases h with ⟨r, hr, p, s, hu, hv⟩
  rcases List.mem_cons.mp hr with hstart | hmapped
  · subst r
    rw [hu, hv]
    simpa [augmentStartRule, projectAugmentString, projectAugmentSymbol,
      List.map_append] using
      (Relation.ReflTransGen.refl :
        g.DerivesRightmost
          (g.projectAugmentString p ++ [symbol.nonterminal g.initial] ++
            s.map symbol.terminal)
          (g.projectAugmentString p ++ [symbol.nonterminal g.initial] ++
            s.map symbol.terminal))
  · rcases List.mem_map.mp hmapped with ⟨r₀, hr₀, heq⟩
    subst r
    apply Relation.ReflTransGen.single
    refine ⟨r₀, hr₀, g.projectAugmentString p, s, ?_, ?_⟩
    · rw [hu]
      simp [augmentRule, projectAugmentString, projectAugmentSymbol]
    · rw [hv]
      simp only [g.projectAugmentString_append,
        g.projectAugmentString_map_terminal]
      have hright : g.projectAugmentString (augmentRule r₀).2 = r₀.2 := by
        exact g.projectAugmentString_augmentString r₀.2
      rw [hright]

/-- Project an augmented rightmost derivation back to the original grammar. -/
public theorem derivesRightmost_project_augment
    {u v : List (symbol T (Option g.nt))}
    (h : g.augment.DerivesRightmost u v) :
    g.DerivesRightmost (g.projectAugmentString u) (g.projectAugmentString v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.trans (derivesRightmost_project_augment_of_produces g hstep)

/-- Fresh-start augmentation preserves the generated language. -/
public theorem augment_language : CF_language g.augment = CF_language g := by
  ext w
  constructor
  · intro hw
    change CF_derives g.augment
      [symbol.nonterminal g.augment.initial]
      (w.map (symbol.terminal (N := Option g.nt))) at hw
    have hp := derives_project_augment g hw
    simpa [projectAugmentString, projectAugmentSymbol] using hp
  · intro hw
    change CF_derives g [symbol.nonterminal g.initial]
      (w.map (symbol.terminal (N := g.nt))) at hw
    have hlift := augment_derives g hw
    simpa using hlift

/-- Knuth's semantic handle-uniqueness condition, before fresh-start
augmentation.

Suppose the first derivation has just used `r₁` after the prefix `p₁`, so
its handle ends after `p₁ ++ r₁.2`.  The equality in the premise says that
the *entire* second right-sentential form can also be split at that first handle
boundary, with a terminal suffix `y`.  If the actual suffix `s₁` of the first
handle and `y` have the same `k` visible terminals, an LR(k) grammar must choose
the same handle position and production.

Allowing the second handle to end later than the first is essential: that is the
case which detects a possible shift instead of the first reduction.  Requiring
only `p₁ ++ r₁.2 = p₂ ++ r₂.2` would detect reduce/reduce conflicts but
miss shift/reduce conflicts.
-/
@[expose]
public def CoreIsLRk (k : ℕ) : Prop :=
  ∀ (r₁ r₂ : g.nt × List (symbol T g.nt)), r₁ ∈ g.rules → r₂ ∈ g.rules →
    ∀ (p₁ p₂ : List (symbol T g.nt)) (s₁ s₂ y : List T),
      g.DerivesRightmost [symbol.nonterminal g.initial]
        (p₁ ++ [symbol.nonterminal r₁.1] ++ s₁.map symbol.terminal) →
      g.DerivesRightmost [symbol.nonterminal g.initial]
        (p₂ ++ [symbol.nonterminal r₂.1] ++ s₂.map symbol.terminal) →
      p₂ ++ r₂.2 ++ s₂.map symbol.terminal =
        p₁ ++ r₁.2 ++ y.map symbol.terminal →
      lrLookahead k s₁ = lrLookahead k y →
      p₁ = p₂ ∧ r₁ = r₂

/-- Semantic LR(k) condition for a context-free grammar.

Handle uniqueness is checked after adjoining a genuinely fresh start symbol and
the production `S′ → S`.  Thus the condition includes conflicts with the accept
action, not only conflicts between original productions.
-/
@[expose]
public def IsLRk (k : ℕ) : Prop :=
  g.augment.CoreIsLRk k

/-- Core LR lookahead is monotone: a grammar satisfying the handle condition
with `k` symbols also satisfies it with any larger lookahead. -/
public theorem CoreIsLRk.mono {k l : ℕ} (hkl : k ≤ l)
    (hg : g.CoreIsLRk k) : g.CoreIsLRk l := by
  intro r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
  exact hg r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform <| by
    simpa [lrLookahead, List.take_take, Nat.min_eq_left hkl] using
      congrArg (List.take k) hlook

/-- LR lookahead is monotone: a grammar that is LR(k) is also LR(l) for any `l ≥ k`. -/
public theorem IsLRk.mono {k l : ℕ} (hkl : k ≤ l) (hg : g.IsLRk k) : g.IsLRk l := by
  exact CoreIsLRk.mono g.augment hkl hg

end CF_grammar

variable {T : Type}

/-- Language class generated by an LR(k) grammar. -/
@[expose]
public def is_LRk (k : ℕ) (L : Language T) : Prop :=
  ∃ g : CF_grammar T, g.IsLRk k ∧ CF_language g = L

/-- The class of languages generated by LR(k) grammars for a fixed amount
of lookahead. -/
@[expose]
public def LRk (k : ℕ) : Set (Language T) :=
  setOf (is_LRk k)

/-- Language class generated by an LR(k) grammar for some finite `k`. -/
@[expose]
public def is_LR (L : Language T) : Prop :=
  ∃ k : ℕ, is_LRk k L

/-- The class of LR languages. -/
@[expose]
public def LR : Set (Language T) :=
  setOf is_LR

/-- Every LR(k) language is an LR language. -/
public theorem is_LR_of_is_LRk {k : ℕ} {L : Language T} (h : is_LRk k L) : is_LR L :=
  ⟨k, h⟩

/-- LR language classes are monotone in the amount of lookahead. -/
public theorem is_LRk_mono {k l : ℕ} (hkl : k ≤ l) {L : Language T}
    (h : is_LRk k L) : is_LRk l L := by
  rcases h with ⟨g, hg, hL⟩
  exact ⟨g, CF_grammar.IsLRk.mono g hkl hg, hL⟩
