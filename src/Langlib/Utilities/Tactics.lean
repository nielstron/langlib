import Langlib.Grammars.ContextFree.Definition
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Utilities.ListUtils

/-! # Custom Tactics for Langlib

This file provides domain-specific tactics that automate common proof patterns
in grammar and language theory formalizations.

## Main declarations

- `no_nonterminal` — close goals where a nonterminal appears in a terminal-only list
- `grammar_cases` — case-split a CF/unrestricted grammar transformation by rule
- `append_chase` — exhaustive analysis of list-append equations
- `count_contra` — contradiction from character-counting arguments
- `derive_step` — construct a single CF derivation step with context
- `replicate_norm` — normalize `List.replicate` and `List.append` expressions
- `deri_context` — strip matching prefix/postfix from a derivation goal
- `language_ext` — prove language equality by extensionality
-/

open Lean Elab Tactic

/-! ## no_nonterminal

Closes goals that are absurd because a `symbol.nonterminal` appears in a list
built from `symbol.terminal` (typically from `List.map symbol.terminal w`).

Automates the recurring pattern:
```
have := congr_arg List.toFinset h
rw [Finset.ext_iff] at this
specialize this (symbol.nonterminal _)
aesop
```
-/

open Meta in
/-- Collect all `symbol.nonterminal _` and `symbol.terminal _` subexpressions from an expression. -/
private partial def collectSymbols (e : Expr) : Array Expr := Id.run do
  let rec go (e : Expr) : StateM (Array Expr) Unit := do
    if e.isApp then
      let fn := e.getAppFn
      if fn.isConst then
        let name := fn.constName!
        if name == ``symbol.nonterminal || name == ``symbol.terminal then
          modify (·.push e)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ e => go e
    | .proj _ _ e => go e
    | _ => pure ()
  let (_, syms) := go e |>.run #[]
  syms

open Meta in
/-- Find list equalities in the local context and try the toFinset trick.
    Iterates over all hypotheses, tries `congr_arg List.toFinset` on each,
    then specializes on every `symbol` constructor found in context. -/
private def noNonterminalFinset : TacticM Unit := do
  -- First call exfalso (may already be proving False)
  try Tactic.evalTactic (← `(tactic| exfalso)) catch _ => pure ()
  -- Collect hypothesis names (only equalities) and symbols from context
  let mvarId ← Tactic.getMainGoal
  let (eqHypNames, syms) ← mvarId.withContext do
    let lctx ← getLCtx
    let mut allSyms : Array Expr := #[]
    let mut eqNames : Array Name := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      allSyms := allSyms ++ collectSymbols ty
      -- Only include hypotheses whose type is an equality
      if ty.isAppOf ``Eq then
        eqNames := eqNames.push ldecl.userName
    allSyms := allSyms ++ collectSymbols (← mvarId.getType)
    -- Prioritize nonterminal symbols first (most likely to produce contradiction)
    let ntSyms := allSyms.filter fun e =>
      e.isApp && e.getAppFn.isConst && e.getAppFn.constName! == ``symbol.nonterminal
    let tSyms := allSyms.filter fun e =>
      e.isApp && e.getAppFn.isConst && e.getAppFn.constName! == ``symbol.terminal
    let ordered := ntSyms ++ tSyms
    let syms := ordered.toList.pwFilter (fun a b => !Lean.Expr.equal a b)
    return (eqNames, syms)
  -- Try each equality hypothesis with each symbol (nonterminals first)
  for hypName in eqHypNames do
    for sym in syms do
      try
        let symStx ← mvarId.withContext (PrettyPrinter.delab sym)
        Tactic.evalTactic (← `(tactic| (
          have _h_fs := congr_arg List.toFinset $(mkIdent hypName);
          rw [Finset.ext_iff] at _h_fs;
          have _h_spec := _h_fs $symStx;
          simp +decide at _h_spec;
          done)))
        return
      catch _ => continue
  throwError "no_nonterminal: could not find a suitable list equality and symbol witness"

open Meta in
/-- Close goals where a `symbol.nonterminal` appears in a terminal-only list.

    This is a metaprogram that:
    1. Scans the local context for hypotheses that could be list equalities
    2. Tries `congr_arg List.toFinset` + `Finset.ext_iff` on each
    3. Collects all `symbol.nonterminal _` / `symbol.terminal _` from context
    4. Tries specializing on each, then `simp +decide` to derive contradiction

    Falls back to `exfalso; simp` for membership-based contradictions. -/
elab "no_nonterminal" : tactic => do
  -- Strategy 1: Try the metaprogram-based Finset approach
  try
    noNonterminalFinset
    return
  catch _ => pure ()
  -- Strategy 2: Try exfalso + simp for membership contradictions
  try
    Elab.Tactic.evalTactic (← `(tactic| (
      exfalso; simp only [List.mem_map, List.mem_append, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, symbol.terminal.injEq, symbol.nonterminal.injEq, reduceCtorEq,
        not_true, not_false_eq_true, exists_eq_left, imp_false, and_false, or_false,
        false_or, false_and] at *)))
    return
  catch _ => pure ()
  -- Strategy 3: Last resort aesop
  try
    Elab.Tactic.evalTactic (← `(tactic| aesop))
    return
  catch _ =>
    throwError "no_nonterminal: all strategies failed"


/-! ## grammar_cases

Given a hypothesis `h : CF_transforms g w w'`, destructure it into the rule,
prefix, suffix, and then case-split on which rule was applied. Finishes by
simplifying with `+decide` to substitute concrete rule data.

For grammars defined as named constants, pass the name as an extra simp lemma
to unfold the rules: `grammar_cases ht [cfg_anbn]`
-/
/-- Core implementation for grammar_cases. Unfolds `CF_transforms`, destructures
    the existentials, uses `simp_all +decide` to resolve concrete rule membership,
    case-splits on which rule was applied, and simplifies each branch.

    For grammars defined as named constants, pass the name as an extra simp lemma
    to unfold the rules: `grammar_cases ht [cfg_anbn]` -/
macro "grammar_cases " h:ident : tactic =>
  `(tactic| (
    simp only [CF_transforms] at $h:ident;
    obtain ⟨r, u_ctx, v_ctx, rule_mem, h_bef, h_aft⟩ := $h:ident;
    (try simp_all +decide);
    (try (rcases rule_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) <;>
    (try subst_vars) <;>
    (try simp_all +decide) <;>
    (try (cases u_ctx <;> simp_all +decide)) <;>
    (try aesop)))

macro "grammar_cases " h:ident " [" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    simp only [CF_transforms] at $h:ident;
    obtain ⟨r, u_ctx, v_ctx, rule_mem, h_bef, h_aft⟩ := $h:ident;
    (try simp_all +decide [$extras,*]);
    (try (rcases rule_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) <;>
    (try subst_vars) <;>
    (try simp_all +decide [$extras,*]) <;>
    (try (cases u_ctx <;> simp_all +decide [$extras,*])) <;>
    (try aesop)))


/-! ## append_chase

Exhaustively analyze list-append equations in hypotheses.

When you have hypotheses like `a ++ b = c ++ d` or `a ++ [x] ++ b = c ++ [y] ++ d`,
this tactic repeatedly applies `List.append_eq_append_iff`, performs case splits,
and simplifies with `simp_all +decide` and `omega`.
-/
macro "append_chase" : tactic =>
  `(tactic| (
    simp only [List.append_assoc] at * <;>
    (try (rw [List.append_eq_append_iff] at *)) <;>
    (try (rw [List.cons_eq_append_iff] at *)) <;>
    (try (rw [List.append_eq_nil_iff] at *)) <;>
    simp_all +decide [List.replicate, List.length_append, List.length_replicate,
      List.map_append, List.map_cons, List.map_nil] <;>
    (try omega)))

/-! ### append_chase variant with extra simp lemmas -/
macro "append_chase " "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    simp only [List.append_assoc] at * <;>
    (try (rw [List.append_eq_append_iff] at *)) <;>
    (try (rw [List.cons_eq_append_iff] at *)) <;>
    (try (rw [List.append_eq_nil_iff] at *)) <;>
    simp_all +decide [List.replicate, List.length_append, List.length_replicate,
      List.map_append, List.map_cons, List.map_nil, $extras,*] <;>
    (try omega)))


/-! ## count_contra

Derive a contradiction from `List.count_in` equalities/inequalities.

Rewrites all `count_in` hypotheses using distributivity over append, replicate,
and singletons, then invokes `omega` to find the contradiction. Useful for
pumping lemma counterexamples where character counts become inconsistent.
-/
macro "count_contra" : tactic =>
  `(tactic| (
    simp +decide [List.count_in_append, List.count_in_replicate_eq,
      List.count_in_replicate_neq, List.count_in_zero_of_notin,
      List.count_in_nil, List.count_in_cons,
      List.count_in_singleton_eq, List.count_in_singleton_neq,
      List.count_in_pos_of_in,
      List.n_times, List.count_in_flatten,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      List.mem_append, not_or,
      Nat.add_zero, Nat.zero_add] at * <;>
    omega))


/-! ## derive_step

Construct a single CF derivation step, automatically wrapping with prefix/postfix
context. Given a rule `r` from the grammar, builds the `CF_transforms` witness.

Usage: `derive_step r`
-/
macro "derive_step " r:term : tactic =>
  `(tactic| (
    first
    | (apply CF_deri_of_tran;
       exact ⟨$r, [], [], by simp +decide, by simp +decide, by simp +decide⟩)
    | (apply CF_deri_of_tran;
       refine ⟨$r, _, _, ?_, ?_, ?_⟩ <;> simp +decide)))


/-! ## replicate_norm

Normalize expressions involving `List.replicate`, `List.append`, `List.map`,
and `List.length`. Handles `replicate_succ`, `replicate_add`, associativity,
and identity laws.
-/
macro "replicate_norm" : tactic =>
  `(tactic| (
    simp only [List.replicate_succ, List.replicate_succ',
      List.replicate_add, List.replicate_zero,
      List.append_nil, List.nil_append,
      List.append_assoc, List.map_append,
      List.map_cons, List.map_nil,
      List.length_replicate, List.length_append,
      List.length_map, List.length_cons, List.length_nil,
      List.singleton_append,
      Nat.add_zero, Nat.zero_add] <;>
    (try ring_nf) <;> (try omega) <;> (try rfl)))


/-! ## deri_context

When the goal is `CF_derives g (pᵣ ++ w₁ ++ pₒ) (pᵣ ++ w₂ ++ pₒ)`,
strip the common prefix and/or postfix, reducing the goal to `CF_derives g w₁ w₂`.

Also handles goals with only a prefix or only a postfix.
-/
macro "deri_context" : tactic =>
  `(tactic| (
    first
    | apply CF_deri_with_prefix_and_postfix
    | apply CF_deri_with_prefix
    | apply CF_deri_with_postfix))


/-! ## language_ext

Prove language (set) equality by extensionality.

Opens the goal with `ext w; constructor`, introducing the membership hypothesis
as `hw` in each direction, then tries `aesop` and `simp_all` to close the goals.
-/
macro "language_ext" : tactic =>
  `(tactic| (
    ext w;
    constructor <;> intro hw <;> (
      first
      | assumption
      | aesop
      | simp_all)))


/-! ## pumping_setup

Set up a pumping lemma argument for showing a language is not context-free.
Given goal `¬ is_CF L`, introduces the pumping length and provides the
decomposition variables `u, v, x, y, z` with their constraints.

After `pumping_setup`, you need to:
1. Provide a witness word
2. Show it's in the language
3. Show it's long enough
4. Derive a contradiction from the pumping property
-/
macro "pumping_setup" : tactic =>
  `(tactic| (
    intro _h_cf;
    obtain ⟨_n_pump, _h_pump⟩ := CF_pumping _h_cf))
