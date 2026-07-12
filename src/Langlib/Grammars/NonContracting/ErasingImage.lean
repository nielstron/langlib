module

public import Langlib.Grammars.NonContracting.Definition
public import Langlib.Grammars.Unrestricted.FiniteNonterminals
public import Langlib.Grammars.Unrestricted.Toolbox
public import Langlib.Utilities.Homomorphism
import Mathlib.Tactic

@[expose]
public section

/-!
# Recursively enumerable languages as erasing images of non-contracting languages

This file implements the standard padding construction for unrestricted grammars.  A rule
whose output is shorter than its input emits enough padding symbols to preserve length.  The
padding symbols then commute to the right and survive as terminals in the generated word; an
erasing homomorphism removes them again.

The construction first restricts the source grammar to its finitely many used nonterminals.
For a grammar with finite terminal and nonterminal alphabets, its simulation uses:

* `some t` for an original terminal `t` and `none` for terminal padding;
* `some A` for an original nonterminal `A` and `none` for the padding nonterminal;
* one padded copy of every source rule;
* rules moving the padding nonterminal rightward across every terminal and nonterminal; and
* one rule converting the padding nonterminal to the padding terminal.

Projection erases padding and recovers every simulated source step.  Conversely, padding can
be moved across the untouched right context after every source step, so every source derivation
lifts to the new grammar.

This is the grammar-theoretic core of the classical fact that every recursively enumerable
language is a homomorphic image of a context-sensitive language.

## Main declarations

* `erasePadding` — the homomorphism deleting the padding terminal;
* `erasingImageGrammar` — the non-contracting padded simulation of an arbitrary grammar;
* `erasingImageGrammar_noncontracting` — every rule of the simulation is non-contracting;
* `erasingImageGrammar_language` — erasing padding recovers the source language;
* `exists_noncontracting_erasingImage` — language-level packaging of the construction.

## Reference

J. E. Hopcroft and J. D. Ullman, *Formal Languages and Their Relation to Automata*,
Theorem 9.9 and Corollary 9.3, 1969.
-/

open Relation

namespace Grammar.ErasingImage

variable {T N : Type}

/-- Delete padding terminals and retain original terminals. -/
public def erasePadding : Option T → List T
  | some t => [t]
  | none => []

/-- Embed one source symbol into the padded grammar. -/
public def liftSymbol : symbol T N → symbol (Option T) (Option N)
  | .terminal t => .terminal (some t)
  | .nonterminal A => .nonterminal (some A)

/-- Embed a source sentential form into the padded grammar symbol by symbol. -/
public def liftString (w : List (symbol T N)) :
    List (symbol (Option T) (Option N)) :=
  w.map liftSymbol

/-- The nonterminal used while padding is moved to the right edge. -/
public def paddingSymbol : symbol (Option T) (Option N) :=
  .nonterminal none

/-- The terminal padding symbol that survives in a generated padded word. -/
public def paddingTerminal : symbol (Option T) (Option N) :=
  .terminal none

/-- Length of a rule's complete left-hand side. -/
public def inputLength (r : grule T N) : ℕ :=
  r.input_L.length + 1 + r.input_R.length

/-- Number of padding symbols needed to make a source rule non-contracting. -/
public def paddingCount (r : grule T N) : ℕ :=
  inputLength r - r.output_string.length

/-- A block of padding nonterminals. -/
public def paddingString (n : ℕ) : List (symbol (Option T) (Option N)) :=
  List.replicate n paddingSymbol

/-- A source rule with enough padding appended to make it non-contracting. -/
public def paddedRule (r : grule T N) : grule (Option T) (Option N) where
  input_L := liftString r.input_L
  input_N := some r.input_N
  input_R := liftString r.input_R
  output_string := liftString r.output_string ++ paddingString (paddingCount r)

/-- Move the padding nonterminal one position to the right across a lifted source symbol. -/
public def swapRule (s : symbol T N) : grule (Option T) (Option N) where
  input_L := []
  input_N := none
  input_R := [liftSymbol s]
  output_string := [liftSymbol s, paddingSymbol]

/-- Convert the padding nonterminal into the padding terminal. -/
public def finishPaddingRule : grule (Option T) (Option N) where
  input_L := []
  input_N := none
  input_R := []
  output_string := [paddingTerminal]

/-- The finite list of source symbols across which padding may have to move. -/
public noncomputable def activeSymbols [Fintype T] [Fintype N] : List (symbol T N) :=
  (Finset.univ.toList.map symbol.terminal) ++
    (Finset.univ.toList.map symbol.nonterminal)

/-- Commuting rules for every symbol of finite terminal and nonterminal alphabets. -/
public noncomputable def swapRules [Fintype T] [Fintype N] :
    List (grule (Option T) (Option N)) :=
  (activeSymbols (T := T) (N := N)).map swapRule

/-- Padded simulation for a grammar whose terminal and nonterminal alphabets are finite. -/
public noncomputable def finiteErasingImageGrammar [Fintype T] (g : grammar T)
    [Fintype g.nt] : grammar (Option T) where
  nt := Option g.nt
  initial := some g.initial
  rules := g.rules.map paddedRule ++ swapRules (T := T) (N := g.nt) ++
    [finishPaddingRule]

@[simp] private theorem liftString_length (w : List (symbol T N)) :
    (liftString w).length = w.length := by
  simp [liftString]

@[simp] private theorem paddingString_length (n : ℕ) :
    (paddingString (T := T) (N := N) n).length = n := by
  simp [paddingString]

private theorem paddedRule_noncontracting (r : grule T N) :
    (paddedRule r).output_string.length ≥
      (paddedRule r).input_L.length + 1 + (paddedRule r).input_R.length := by
  simp only [paddedRule, liftString_length,
    List.length_append, paddingString_length, paddingCount, inputLength]
  omega

private theorem swapRule_noncontracting (s : symbol T N) :
    (swapRule s).output_string.length ≥
      (swapRule s).input_L.length + 1 + (swapRule s).input_R.length := by
  simp [swapRule]

private theorem finishPaddingRule_noncontracting :
    (finishPaddingRule (T := T) (N := N)).output_string.length ≥
      (finishPaddingRule (T := T) (N := N)).input_L.length + 1 +
        (finishPaddingRule (T := T) (N := N)).input_R.length := by
  simp [finishPaddingRule]

/-- Every rule of the finite padded simulation is non-contracting. -/
public theorem finiteErasingImageGrammar_noncontracting [Fintype T]
    (g : grammar T) [Fintype g.nt] :
    grammar_noncontracting (finiteErasingImageGrammar g) := by
  classical
  intro r hr
  simp only [finiteErasingImageGrammar, swapRules, List.mem_append, List.mem_map,
    List.mem_singleton] at hr
  rcases hr with (⟨r₀, _hr₀, rfl⟩ | ⟨s, _hs, rfl⟩) | rfl
  · exact paddedRule_noncontracting r₀
  · exact swapRule_noncontracting s
  · exact finishPaddingRule_noncontracting

/-! ## Projection and soundness -/

/-- Project a padded-grammar symbol back to zero or one source symbols. -/
private def projectSymbol : symbol (Option T) (Option N) → List (symbol T N)
  | .terminal (some t) => [.terminal t]
  | .terminal none => []
  | .nonterminal (some A) => [.nonterminal A]
  | .nonterminal none => []

private def projectString (w : List (symbol (Option T) (Option N))) :
    List (symbol T N) :=
  w.flatMap projectSymbol

@[simp] private theorem projectString_nil :
    projectString ([] : List (symbol (Option T) (Option N))) = [] := by
  rfl

@[simp] private theorem projectString_cons
    (s : symbol (Option T) (Option N)) (w : List (symbol (Option T) (Option N))) :
    projectString (s :: w) = projectSymbol s ++ projectString w := by
  simp [projectString]

@[simp] private theorem projectString_append
    (u v : List (symbol (Option T) (Option N))) :
    projectString (u ++ v) = projectString u ++ projectString v := by
  simp [projectString, List.flatMap_append]

@[simp] private theorem projectSymbol_liftSymbol (s : symbol T N) :
    projectSymbol (liftSymbol s) = [s] := by
  cases s <;> rfl

@[simp] private theorem projectString_liftString (w : List (symbol T N)) :
    projectString (liftString w) = w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      change projectString (liftSymbol s :: liftString w) = s :: w
      simp [ih]

@[simp] private theorem flatMap_projectSymbol_map_liftSymbol
    (w : List (symbol T N)) :
    List.flatMap projectSymbol (List.map liftSymbol w) = w := by
  simpa [projectString, liftString] using projectString_liftString w

@[simp] private theorem projectSymbol_paddingSymbol :
    projectSymbol (paddingSymbol (T := T) (N := N)) = [] := by
  rfl

@[simp] private theorem projectSymbol_paddingTerminal :
    projectSymbol (paddingTerminal (T := T) (N := N)) = [] := by
  rfl

@[simp] private theorem projectString_paddingString (n : ℕ) :
    projectString (paddingString (T := T) (N := N) n) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change projectString (paddingSymbol :: paddingString n) = []
      simp [ih]

@[simp] private theorem flatMap_projectSymbol_replicate_paddingSymbol (n : ℕ) :
    List.flatMap projectSymbol
      (List.replicate n (paddingSymbol (T := T) (N := N))) = [] := by
  change projectString (paddingString (T := T) (N := N) n) = []
  exact projectString_paddingString (T := T) (N := N) n

/-- One padded simulation step projects either to one source step or to equality. -/
private theorem project_transforms [Fintype T] (g : grammar T) [Fintype g.nt]
    {u v : List (symbol (Option T) (Option g.nt))}
    (h : grammar_transforms (finiteErasingImageGrammar g) u v) :
    grammar_derives g (projectString u) (projectString v) := by
  classical
  rcases h with ⟨r, hr, left, right, hu, hv⟩
  simp only [finiteErasingImageGrammar, swapRules, List.mem_append, List.mem_map,
    List.mem_singleton] at hr
  rcases hr with (⟨r₀, hr₀, rfl⟩ | ⟨s, _hs, rfl⟩) | rfl
  · apply Relation.ReflTransGen.single
    refine ⟨r₀, hr₀, projectString left, projectString right, ?_, ?_⟩
    · rw [hu]
      simp [projectString, projectSymbol, paddedRule, liftString, paddingString,
        List.flatMap_append, List.append_assoc]
    · rw [hv]
      simp [projectString, paddedRule, liftString, paddingString,
        List.flatMap_append, List.append_assoc]
  · have heq : projectString u = projectString v := by
      rw [hu, hv]
      simp [projectString, projectSymbol, swapRule, liftSymbol, paddingSymbol,
        List.flatMap_append, List.append_assoc]
    rw [heq]
    exact Relation.ReflTransGen.refl
  · have heq : projectString u = projectString v := by
      rw [hu, hv]
      simp [projectString, projectSymbol, finishPaddingRule, paddingTerminal,
        List.flatMap_append, List.append_assoc]
    rw [heq]
    exact Relation.ReflTransGen.refl

/-- Every derivation of the padded simulation projects to a source derivation. -/
private theorem project_derives [Fintype T] (g : grammar T) [Fintype g.nt]
    {u v : List (symbol (Option T) (Option g.nt))}
    (h : grammar_derives (finiteErasingImageGrammar g) u v) :
    grammar_derives g (projectString u) (projectString v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h step ih =>
      exact Relation.ReflTransGen.trans ih (project_transforms g step)

/-! ## Padding motion and completeness -/

private theorem paddedRule_mem [Fintype T] (g : grammar T) [Fintype g.nt]
    {r : grule T g.nt} (hr : r ∈ g.rules) :
    paddedRule r ∈ (finiteErasingImageGrammar g).rules := by
  classical
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

private theorem swapRule_mem [Fintype T] (g : grammar T) [Fintype g.nt]
    (s : symbol T g.nt) :
    swapRule s ∈ (finiteErasingImageGrammar g).rules := by
  classical
  have hs : s ∈ activeSymbols (T := T) (N := g.nt) := by
    cases s with
    | terminal t => simp [activeSymbols]
    | nonterminal A => simp [activeSymbols]
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

private theorem finishPaddingRule_mem [Fintype T] (g : grammar T) [Fintype g.nt] :
    finishPaddingRule ∈ (finiteErasingImageGrammar g).rules := by
  classical
  simp [finiteErasingImageGrammar]

private theorem swap_transforms [Fintype T] (g : grammar T) [Fintype g.nt]
    (s : symbol T g.nt) (tail : List (symbol (Option T) (Option g.nt))) :
    grammar_transforms (finiteErasingImageGrammar g)
      (paddingSymbol :: liftSymbol s :: tail)
      (liftSymbol s :: paddingSymbol :: tail) := by
  refine ⟨swapRule s, swapRule_mem g s, [], tail, ?_, ?_⟩ <;>
    simp [swapRule, paddingSymbol]

/-- Move one padding nonterminal rightward across a lifted source string. -/
private theorem move_one_padding [Fintype T] (g : grammar T) [Fintype g.nt]
    (w : List (symbol T g.nt)) (tail : List (symbol (Option T) (Option g.nt))) :
    grammar_derives (finiteErasingImageGrammar g)
      (paddingSymbol :: liftString w ++ tail)
      (liftString w ++ paddingSymbol :: tail) := by
  induction w generalizing tail with
  | nil =>
      simpa [liftString] using
        (Relation.ReflTransGen.refl :
          grammar_derives (finiteErasingImageGrammar g)
            (paddingSymbol :: tail) (paddingSymbol :: tail))
  | cons s w ih =>
      have hstep := Relation.ReflTransGen.single
        (swap_transforms g s (liftString w ++ tail))
      have hrest := grammar_deri_with_prefix [liftSymbol s] (ih tail)
      simpa [liftString, List.append_assoc] using
        Relation.ReflTransGen.trans hstep hrest

/-- Move a block of padding nonterminals rightward across a lifted source string. -/
private theorem move_padding [Fintype T] (g : grammar T) [Fintype g.nt]
    (n : ℕ) (w : List (symbol T g.nt))
    (tail : List (symbol (Option T) (Option g.nt))) :
    grammar_derives (finiteErasingImageGrammar g)
      (paddingString n ++ liftString w ++ tail)
      (liftString w ++ paddingString n ++ tail) := by
  induction n generalizing tail with
  | zero =>
      simpa [paddingString] using
        (Relation.ReflTransGen.refl :
          grammar_derives (finiteErasingImageGrammar g)
            (liftString w ++ tail) (liftString w ++ tail))
  | succ n ih =>
      have hrest := grammar_deri_with_prefix [paddingSymbol] (ih tail)
      have hone := move_one_padding g w (paddingString n ++ tail)
      have hrest' : grammar_derives (finiteErasingImageGrammar g)
          (paddingSymbol :: paddingString n ++ liftString w ++ tail)
          (paddingSymbol :: liftString w ++ paddingString n ++ tail) := by
        simpa [List.append_assoc] using hrest
      have hone' : grammar_derives (finiteErasingImageGrammar g)
          (paddingSymbol :: liftString w ++ paddingString n ++ tail)
          (liftString w ++ paddingSymbol :: paddingString n ++ tail) := by
        simpa [List.append_assoc] using hone
      simpa [paddingString, List.replicate_succ, List.append_assoc] using
        Relation.ReflTransGen.trans hrest' hone'

/-- Simulate one source step from a lifted sentential form, commuting the newly emitted
padding past the untouched right context. -/
private theorem lift_transforms [Fintype T] (g : grammar T) [Fintype g.nt]
    {u v : List (symbol T g.nt)} (h : grammar_transforms g u v) (k : ℕ) :
    ∃ d : ℕ,
      grammar_derives (finiteErasingImageGrammar g)
        (liftString u ++ paddingString k)
        (liftString v ++ paddingString (d + k)) := by
  rcases h with ⟨r, hr, left, right, hu, hv⟩
  let d := paddingCount r
  let pre := liftString left ++ liftString r.output_string
  have hstep : grammar_transforms (finiteErasingImageGrammar g)
      (liftString u ++ paddingString k)
      (pre ++ paddingString d ++ liftString right ++ paddingString k) := by
    refine ⟨paddedRule r, paddedRule_mem g hr, liftString left,
      liftString right ++ paddingString k, ?_, ?_⟩
    · simp [hu, paddedRule, liftString, liftSymbol, List.map_append, List.append_assoc]
    · simp [pre, d, paddedRule, liftString, List.append_assoc]
  have hmove := grammar_deri_with_prefix pre
    (move_padding g d right (paddingString k))
  have hmove' : grammar_derives (finiteErasingImageGrammar g)
      (pre ++ paddingString d ++ liftString right ++ paddingString k)
      (pre ++ liftString right ++ paddingString d ++ paddingString k) := by
    simpa [List.append_assoc] using hmove
  refine ⟨d, ?_⟩
  have hsim := Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single hstep) hmove'
  have htarget :
      pre ++ liftString right ++ paddingString d ++ paddingString k =
        liftString v ++ paddingString (d + k) := by
    rw [hv]
    simp only [pre, liftString, List.map_append, paddingString, List.replicate_add]
    simp only [List.append_assoc]
  rw [← htarget]
  exact hsim

/-- Every source derivation lifts to a padded derivation, with some accumulated padding at the
right edge. -/
private theorem lift_derives [Fintype T] (g : grammar T) [Fintype g.nt]
    {u v : List (symbol T g.nt)} (h : grammar_derives g u v) :
    ∃ k : ℕ,
      grammar_derives (finiteErasingImageGrammar g)
        (liftString u) (liftString v ++ paddingString k) := by
  induction h with
  | refl =>
      refine ⟨0, ?_⟩
      simpa [paddingString] using
        (Relation.ReflTransGen.refl :
          grammar_derives (finiteErasingImageGrammar g) (liftString u) (liftString u))
  | tail h step ih =>
      rcases ih with ⟨k, hk⟩
      rcases lift_transforms g step k with ⟨d, hd⟩
      exact ⟨d + k, Relation.ReflTransGen.trans hk hd⟩

private theorem finish_padding_transforms [Fintype T] (g : grammar T) [Fintype g.nt]
    (tail : List (symbol (Option T) (Option g.nt))) :
    grammar_transforms (finiteErasingImageGrammar g)
      (paddingSymbol :: tail) (paddingTerminal :: tail) := by
  refine ⟨finishPaddingRule, finishPaddingRule_mem g, [], tail, ?_, ?_⟩ <;>
    simp [finishPaddingRule, paddingSymbol, paddingTerminal]

private theorem finish_padding [Fintype T] (g : grammar T) [Fintype g.nt]
    (n : ℕ) :
    grammar_derives (finiteErasingImageGrammar g)
      (paddingString n) (List.replicate n paddingTerminal) := by
  induction n with
  | zero =>
      simpa [paddingString] using
        (Relation.ReflTransGen.refl :
          grammar_derives (finiteErasingImageGrammar g) [] [])
  | succ n ih =>
      have hstep := Relation.ReflTransGen.single
        (finish_padding_transforms g (paddingString n))
      have hrest := grammar_deri_with_prefix [paddingTerminal] ih
      simpa [paddingString, List.replicate_succ] using
        Relation.ReflTransGen.trans hstep hrest

/-! ## Language equivalence -/

private def paddedTerminalWord (w : List T) (k : ℕ) : List (Option T) :=
  w.map some ++ List.replicate k none

@[simp] private theorem projectString_terminalWord (w : List (Option T)) :
    projectString (N := N) (w.map symbol.terminal) =
      (w.flatMap erasePadding).map symbol.terminal := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases a with
      | none =>
          change projectString (symbol.terminal none :: w.map symbol.terminal) = _
          simp [projectSymbol, erasePadding, ih]
      | some t =>
          change projectString (symbol.terminal (some t) :: w.map symbol.terminal) = _
          simp [projectSymbol, erasePadding, ih]

@[simp] private theorem erasePadding_paddedTerminalWord (w : List T) (k : ℕ) :
    (paddedTerminalWord w k).flatMap erasePadding = w := by
  have hsome : (w.map some).flatMap erasePadding = w := by
    induction w with
    | nil => rfl
    | cons t w ih => simp [erasePadding, ih]
  have hnone : (List.replicate k (none : Option T)).flatMap erasePadding =
      ([] : List T) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, erasePadding, ih]
  simp [paddedTerminalWord, List.flatMap_append, hsome, hnone]

/-- Every generated source word has a generated padded representative. -/
private theorem finite_generates_padded [Fintype T] (g : grammar T) [Fintype g.nt]
    {w : List T} (hw : grammar_generates g w) :
    ∃ k : ℕ,
      grammar_generates (finiteErasingImageGrammar g) (paddedTerminalWord w k) := by
  rcases lift_derives g hw with ⟨k, hk⟩
  have hfinish := grammar_deri_with_prefix
    (liftString (w.map symbol.terminal)) (finish_padding g k)
  have hall := Relation.ReflTransGen.trans hk hfinish
  refine ⟨k, ?_⟩
  simpa [grammar_generates, finiteErasingImageGrammar, paddedTerminalWord,
    liftString, liftSymbol, paddingTerminal, List.map_append, List.map_map] using hall

/-- Erasing padding from a generated simulated word yields a word of the source grammar. -/
private theorem finite_generates_project [Fintype T] (g : grammar T) [Fintype g.nt]
    {w : List (Option T)}
    (hw : grammar_generates (finiteErasingImageGrammar g) w) :
    grammar_generates g (w.flatMap erasePadding) := by
  have hproject := project_derives g hw
  rw [projectString_terminalWord] at hproject
  simpa [grammar_generates, finiteErasingImageGrammar, projectString, projectSymbol,
    liftSymbol] using hproject

private theorem mem_prod_singletons_iff_flatMap {A B : Type}
    (w : List A) (h : A → List B) (u : List B) :
    u ∈ (w.map fun a => ({h a} : Language B)).prod ↔ u = w.flatMap h := by
  induction w generalizing u with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons, Language.mul_def]
      constructor
      · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        rw [Set.mem_singleton_iff] at hu₁
        rw [hu₁, List.flatMap_cons]
        congr 1
        exact (ih u₂).mp hu₂
      · intro hu
        refine ⟨h a, Set.mem_singleton _, w.flatMap h, (ih _).mpr rfl, ?_⟩
        simpa [List.flatMap_cons] using hu.symm

private theorem mem_homomorphicImage_iff_flatMap {A B : Type}
    (L : Language A) (h : A → List B) (u : List B) :
    u ∈ L.homomorphicImage h ↔ ∃ w ∈ L, w.flatMap h = u := by
  simp only [Language.homomorphicImage, Language.subst]
  constructor
  · rintro ⟨w, hw, hu⟩
    exact ⟨w, hw, ((mem_prod_singletons_iff_flatMap w h u).mp hu).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (mem_prod_singletons_iff_flatMap w h _).mpr rfl⟩

/-- Erasing the padding terminals from the finite padded simulation recovers exactly the
source grammar's language. -/
public theorem finiteErasingImageGrammar_language [Fintype T]
    (g : grammar T) [Fintype g.nt] :
    (grammar_language (finiteErasingImageGrammar g)).homomorphicImage erasePadding =
      grammar_language g := by
  ext w
  rw [mem_homomorphicImage_iff_flatMap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact finite_generates_project g hx
  · intro hw
    rcases finite_generates_padded g hw with ⟨k, hk⟩
    exact ⟨paddedTerminalWord w k, hk, erasePadding_paddedTerminalWord w k⟩

/-- The padded simulation of an arbitrary grammar.  Restricting to the nonterminals occurring
in its finite rule list supplies the finite alphabet needed to enumerate the commuting rules. -/
public noncomputable def erasingImageGrammar [Fintype T] (g : grammar T) :
    grammar (Option T) :=
  finiteErasingImageGrammar (restrictGrammar g)

/-- The padded simulation of an arbitrary grammar is non-contracting. -/
public theorem erasingImageGrammar_noncontracting [Fintype T] (g : grammar T) :
    grammar_noncontracting (erasingImageGrammar g) := by
  simpa [erasingImageGrammar] using
    finiteErasingImageGrammar_noncontracting (restrictGrammar g)

/-- Erasing padding from the padded simulation of an arbitrary grammar recovers its language. -/
public theorem erasingImageGrammar_language [Fintype T] (g : grammar T) :
    (grammar_language (erasingImageGrammar g)).homomorphicImage erasePadding =
      grammar_language g := by
  rw [erasingImageGrammar, finiteErasingImageGrammar_language]
  exact (grammar_language_eq_restrictGrammar g).symm

/-- Every unrestricted grammar language is the erasing homomorphic image of a
non-contracting language. -/
public theorem exists_noncontracting_erasingImage [Fintype T] (g : grammar T) :
    ∃ K : Language (Option T),
      is_noncontracting K ∧ K.homomorphicImage erasePadding = grammar_language g := by
  refine ⟨grammar_language (erasingImageGrammar g), ?_, erasingImageGrammar_language g⟩
  exact ⟨erasingImageGrammar g, erasingImageGrammar_noncontracting g, rfl⟩

end Grammar.ErasingImage
