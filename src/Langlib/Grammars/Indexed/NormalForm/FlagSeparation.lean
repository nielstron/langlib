module

public import Mathlib
public import Langlib.Grammars.Indexed.Definition
@[expose]
public section

/-! # Flag Separation for Indexed Grammars

This file constructs a flag-separation transformation for indexed grammars.

This is Step 4 of Aho's Normal Form theorem.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section FlagSeparation

variable (g : IndexedGrammar T)

/-- Does this RHS symbol have a flag push? -/
def hasPush : IRhsSymbol T g.nt g.flag → Bool
  | .nonterminal _ (some _) => true
  | _ => false

/-- Lift an RHS symbol to the new nonterminal type, keeping flags. -/
def fsLiftRhsSym : IRhsSymbol T g.nt g.flag → IRhsSymbol T (g.nt ⊕ (Nat × Nat)) g.flag
  | .terminal t => .terminal t
  | .nonterminal n f => .nonterminal (Sum.inl n) f

/-- Replace a pushed nonterminal with a fresh intermediate (no push). -/
def fsReplaceRhsSym (ruleIdx posIdx : Nat) :
    IRhsSymbol T g.nt g.flag → IRhsSymbol T (g.nt ⊕ (Nat × Nat)) g.flag
  | .terminal t => .terminal t
  | .nonterminal n none => .nonterminal (Sum.inl n) none
  | .nonterminal _ (some _) => .nonterminal (Sum.inr (ruleIdx, posIdx)) none

/-- Strip flag push from an RHS symbol in the lifted type. -/
def fsStripPushRhsSym :
    IRhsSymbol T g.nt g.flag → IRhsSymbol T (g.nt ⊕ (Nat × Nat)) g.flag
  | .terminal t => .terminal t
  | .nonterminal n _ => .nonterminal (Sum.inl n) none

/-- Transform a single rule at index `i` into flag-separated rules.

Note: The consume check is done first (before the terminal check) to ensure
that rules with `consume = some` and terminal RHS are properly separated.
This is required for `flagSeparate_flagsSeparated` to hold. -/
def fsSingleRule (i : Nat) (r : IRule T g.nt g.flag) :
    List (IRule T (g.nt ⊕ (Nat × Nat)) g.flag) :=
  -- Case 1: Consumes a flag
  if r.consume.isSome then
    let hasAnyPush := r.rhs.any (g.hasPush)
    if hasAnyPush then
      -- A[f·] → C_{i,0}, C_{i,0} → [RHS with pushes replaced by intermediates]
      -- Plus push rules for each pushed position
      let consumeRule : IRule T _ _ :=
        ⟨Sum.inl r.lhs, r.consume, [.nonterminal (Sum.inr (i, 0)) none]⟩
      let intermediateRhs := (r.rhs.zipIdx).map fun ⟨s, j⟩ =>
        g.fsReplaceRhsSym i (j + 1) s
      let intermediateRule : IRule T _ _ :=
        ⟨Sum.inr (i, 0), none, intermediateRhs⟩
      let pushRules := (r.rhs.zipIdx).filterMap fun ⟨s, j⟩ =>
        match s with
        | .nonterminal n (some f) =>
            some ⟨Sum.inr (i, j + 1), (none : Option g.flag),
                  [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩
        | _ => none
      consumeRule :: intermediateRule :: pushRules
    else
      -- No pushes, just separate the consume
      let consumeRule : IRule T _ _ :=
        ⟨Sum.inl r.lhs, r.consume, [.nonterminal (Sum.inr (i, 0)) none]⟩
      let passRule : IRule T _ _ :=
        ⟨Sum.inr (i, 0), none, r.rhs.map g.fsStripPushRhsSym⟩
      [consumeRule, passRule]
  -- Case 2: No consumption
  else
    let hasAnyPush := r.rhs.any (g.hasPush)
    if !hasAnyPush then
      -- No pushes at all — already flag-separated, just lift
      [{ lhs := Sum.inl r.lhs, consume := r.consume, rhs := r.rhs.map g.fsLiftRhsSym }]
    else if r.rhs.length == 1 then
      -- Single nonterminal with push — already flag-separated (A → B[f·])
      [{ lhs := Sum.inl r.lhs, consume := r.consume, rhs := r.rhs.map g.fsLiftRhsSym }]
    else
      -- Multiple nonterminals with at least one push — separate all pushes
      let newRhs := (r.rhs.zipIdx).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s
      let mainRule : IRule T _ _ := ⟨Sum.inl r.lhs, none, newRhs⟩
      let pushRules := (r.rhs.zipIdx).filterMap fun ⟨s, j⟩ =>
        match s with
        | .nonterminal n (some f) =>
            some ⟨Sum.inr (i, j), (none : Option g.flag),
                  [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩
        | _ => none
      mainRule :: pushRules

/-- The flag-separated grammar. -/
def flagSeparate : IndexedGrammar T where
  nt := g.nt ⊕ (Nat × Nat)
  flag := g.flag
  initial := Sum.inl g.initial
  rules := ((g.rules.zipIdx).map fun ⟨r, i⟩ => g.fsSingleRule i r).flatten

/-! ### Properties -/

/-- Lift a sentential-form symbol. -/
def fsLiftISym : g.ISym → (g.flagSeparate).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (Sum.inl n) σ

/-- Project a sentential-form symbol. -/
def fsProjISym : (g.flagSeparate).ISym → g.ISym
  | .terminal t => .terminal t
  | .indexed (Sum.inl n) σ => .indexed n σ
  | .indexed (Sum.inr _) σ => .indexed g.initial σ

/-
junk for intermediates

Every rule produced by fsSingleRule has non-empty RHS.
-/
theorem fsSingleRule_rhs_ne_nil (i : Nat) (r : IRule T g.nt g.flag)
    (hr : r.rhs ≠ []) (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    r'.rhs ≠ [] := by
  unfold IndexedGrammar.fsSingleRule at hr';
  aesop

theorem flagSeparate_noEpsilon (hne : g.NoEpsilon') :
    (g.flagSeparate).NoEpsilon' := by
  -- Unfold the definition of NoEpsilon' for the flag-separated grammar (flagSeparate).
  unfold NoEpsilon';
  unfold flagSeparate;
  simp +zetaDelta at *;
  intros r x i hi hr; exact fsSingleRule_rhs_ne_nil g i x ( by
    exact hne x ( by simpa using List.mem_iff_get.mp hi |> fun ⟨ k, hk ⟩ => by aesop ) ) r hr;

/-
fsReplaceRhsSym always produces nonterminals when input is nonterminal.
-/
theorem fsReplaceRhsSym_nonterminal (ri pi : Nat) (n : g.nt) (f : Option g.flag) :
    ∃ n' f', g.fsReplaceRhsSym ri pi (.nonterminal n f) = IRhsSymbol.nonterminal n' f' := by
  cases f <;> tauto

/-
fsStripPushRhsSym always produces nonterminals when input is nonterminal.
-/
theorem fsStripPushRhsSym_nonterminal (n : g.nt) (f : Option g.flag) :
    ∃ n', g.fsStripPushRhsSym (.nonterminal n f) = IRhsSymbol.nonterminal n' none := by
  exact ⟨ Sum.inl n, rfl ⟩

/-
fsLiftRhsSym preserves the terminal/nonterminal nature.
-/
theorem fsLiftRhsSym_nonterminal (n : g.nt) (f : Option g.flag) :
    ∃ n' f', g.fsLiftRhsSym (.nonterminal n f) = IRhsSymbol.nonterminal n' f' := by
  exact ⟨ _, _, rfl ⟩

theorem fsLiftRhsSym_terminal (t : T) :
    g.fsLiftRhsSym (.terminal t) = IRhsSymbol.terminal t := by
  rfl

/-
If all elements of l are nonterminals, then all elements of
    l.zipIdx.map (fsReplaceRhsSym ...) are nonterminals.
-/
theorem fsReplaceRhsSym_map_all_nt (ri : Nat)
    (l : List (IRhsSymbol T g.nt g.flag))
    (h : ∀ s ∈ l, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    ∀ s ∈ (l.zipIdx).map (fun ⟨s, j⟩ => g.fsReplaceRhsSym ri j s),
    ∃ n f, s = IRhsSymbol.nonterminal n f := by
  simp +zetaDelta at *;
  intros s x j hx hs; rcases h x (by
  rw [ List.mem_iff_get ] at hx; aesop;) with ⟨n, f, rfl⟩; (
  cases f <;> aesop)

/-
If all elements of l are nonterminals, then all elements of
    l.map fsLiftRhsSym are nonterminals.
-/
theorem fsLiftRhsSym_map_all_nt
    (l : List (IRhsSymbol T g.nt g.flag))
    (h : ∀ s ∈ l, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    ∀ s ∈ l.map g.fsLiftRhsSym,
    ∃ n f, s = IRhsSymbol.nonterminal n f := by
  intro s hs; rw [ List.mem_map ] at hs; obtain ⟨ s', hs', rfl ⟩ := hs; obtain ⟨ n, f, rfl ⟩ := h s' hs'; exact fsLiftRhsSym_nonterminal g n f;

/-
If all elements of l are nonterminals, then all elements of
    l.map fsStripPushRhsSym are nonterminals.
-/
theorem fsStripPushRhsSym_map_all_nt
    (l : List (IRhsSymbol T g.nt g.flag))
    (h : ∀ s ∈ l, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    ∀ s ∈ l.map g.fsStripPushRhsSym,
    ∃ n f, s = IRhsSymbol.nonterminal n f := by
  intro s hs;
  rw [ List.mem_map ] at hs; obtain ⟨ s, hs₁, hs₂ ⟩ := hs; specialize h s hs₁; aesop;

/-
If the terminal-branch condition is false, hti gives the right case (all nonterminals).
-/
theorem hti_all_nt_of_not_terminal_cond (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f))
    (h : ¬(r.rhs.any (fun s => match s with | .terminal _ => true | _ => false) &&
           r.rhs.length == 1) = true) :
    ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f := by
  exact hti.resolve_left fun ⟨ a, ha ⟩ => h <| by simp +decide [ ha ] ;

/-
Every rule produced by fsSingleRule satisfies TerminalsIsolated.

Push rules from filterMap always produce terminal-isolated rules.
-/
private theorem fsSingleRule_ti_pushRule
    (s : IRhsSymbol T g.nt g.flag) (j : Nat) (offset : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : (match s with
      | .nonterminal n (some f) =>
          some ⟨Sum.inr (i, j + offset), (none : Option g.flag),
                [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩
      | _ => none) = some r') :
    (∃ a : T, r'.rhs = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ r'.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  grind

/-
The pass rule (from consume-no-push case) is terminal-isolated.
-/
private theorem fsSingleRule_ti_passRule (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f)) :
    (∃ a : T, (r.rhs.map g.fsStripPushRhsSym) = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ r.rhs.map g.fsStripPushRhsSym, ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  cases hti;
  · aesop;
  · exact Or.inr ( fsStripPushRhsSym_map_all_nt _ _ ‹_› )

/-
The intermediate rule (from consume-push case) is terminal-isolated.
-/
private theorem fsSingleRule_ti_intermediateRule (r : IRule T g.nt g.flag) (i : Nat)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f)) :
    (∃ a : T, ((r.rhs.zipIdx).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s) = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ (r.rhs.zipIdx).map (fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s),
      ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  rcases hti with ( ⟨ a, ha ⟩ | hti );
  · grind +locals;
  · refine Or.inr fun s hs => ?_;
    rw [ List.mem_map ] at hs; obtain ⟨ x, hx, rfl ⟩ := hs; rcases x with ⟨ x, j ⟩ ;
    rcases hti x ( by rw [ List.mem_iff_get ] at hx; aesop ) with ⟨ n, f, rfl ⟩ ; exact g.fsReplaceRhsSym_nonterminal i ( j + 1 ) n f;

/-
If r' comes from the push-rules filterMap (with any offset), it's terminal-isolated.
-/
private theorem fsSingleRule_ti_filterMap_push (i offset : Nat)
    (l : List (IRhsSymbol T g.nt g.flag × Nat))
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ l.filterMap fun ⟨s, j⟩ =>
      match s with
      | .nonterminal n (some f) =>
          some ⟨Sum.inr (i, j + offset), (none : Option g.flag),
                [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩
      | _ => none) :
    (∃ a : T, r'.rhs = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ r'.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  grind

set_option maxHeartbeats 400000 in
theorem fsSingleRule_terminalsIsolated (i : Nat) (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f))
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    (∃ a : T, r'.rhs = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ r'.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  cases r';
  unfold IndexedGrammar.fsSingleRule at hr';
  split_ifs at hr' <;> simp_all +decide only;
  · split_ifs at hr';
    · rename_i h₁ h₂ h₃;
      cases hr';
      · exact Or.inr fun s hs => by aesop;
      · rename_i h;
        have := fsSingleRule_ti_intermediateRule g r i hti;
        cases h ; aesop;
        rename_i h;
        have := fsSingleRule_ti_filterMap_push g i 1 r.rhs.zipIdx _ h;
        exact this;
    · cases hr' <;> simp_all +decide [List.mem_cons];
      rename_i k hk₁ hk₂ hk₃;
      cases hk₃;
      · rcases hti with ( ⟨ a, ha ⟩ | hti ) <;> simp_all +decide [ List.map ];
        · exact Or.inl ⟨ a, rfl ⟩;
        · exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := hti s hs; exact Or.inl ⟨ n, none, rfl ⟩ ;
      · contradiction;
  · grind +suggestions;
  · split_ifs at hr';
    · cases hti <;> simp_all +decide;
      · grind;
      · exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := ‹∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f› s hs; exact Or.inl ⟨ n, f, rfl ⟩ ;
    · cases hr';
      · exact Or.inr ( fsReplaceRhsSym_map_all_nt g i r.rhs ( hti.elim ( fun ⟨ a, ha ⟩ => by aesop ) fun h => h ) );
      · rename_i h₁ h₂ h₃ h₄;
        exact fsSingleRule_ti_filterMap_push g i 0 _ _ h₄

theorem flagSeparate_terminalsIsolated (hti : g.TerminalsIsolated) :
    (g.flagSeparate).TerminalsIsolated := by
  -- Apply the hypothesis `hti` to the rule `r` in the original grammar.
  intros r' hr'
  obtain ⟨r, hr⟩ := List.mem_flatten.mp hr';
  rcases hr with ⟨ hr₁, hr₂ ⟩;
  rw [ List.mem_map ] at hr₁;
  rcases hr₁ with ⟨ ⟨ r, i ⟩, hr₁, rfl ⟩;
  exact fsSingleRule_terminalsIsolated g i r ( hti r ( by rw [ List.mem_iff_get ] at hr₁; aesop ) ) r' hr₂

/-
Helper: consume rule from Case 2 is flag-separated.
-/
private theorem fsSingleRule_fs_consumeRule (r : IRule T g.nt g.flag) (i : Nat)
    (hc : r.consume.isSome) :
    IRule.FlagsSeparated
      (⟨Sum.inl r.lhs, r.consume,
        [IRhsSymbol.nonterminal (Sum.inr (i, 0)) none]⟩ :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  unfold IRule.FlagsSeparated;
  grind

/-
Helper: intermediate rule from Case 2a is flag-separated.
-/
private theorem fsSingleRule_fs_intermediateRule (r : IRule T g.nt g.flag) (i : Nat)
    (hti : ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    IRule.FlagsSeparated
      (⟨Sum.inr (i, 0), none,
        (r.rhs.zipIdx).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s⟩ :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  -- In this case, all nonterminals in the new RHS have no flag push.
  have h_no_push : ∀ s ∈ r.rhs.zipIdx.map (fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s), ∃ n, s = IRhsSymbol.nonterminal n none := by
    intro s hs
    obtain ⟨x, hx⟩ := List.mem_map.mp hs
    obtain ⟨s', j, hj⟩ : ∃ s' j, x = (s', j) ∧ s' ∈ r.rhs := by
      grind;
    rcases hti s' hj.2 with ⟨ n, f, rfl ⟩ ; unfold fsReplaceRhsSym at hx ; aesop;
  exact ⟨ by tauto, by tauto ⟩

/-
Helper: push rule is flag-separated.
-/
private theorem fsSingleRule_fs_pushRule (n : g.nt) (f : g.flag) (idx : g.nt ⊕ (Nat × Nat)) :
    IRule.FlagsSeparated
      (⟨idx, (none : Option g.flag),
        [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩ :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  constructor <;> aesop

/-
Helper: pass rule from Case 2b is flag-separated.
-/
private theorem fsSingleRule_fs_passRule (r : IRule T g.nt g.flag) (i : Nat)
    (hti : ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    IRule.FlagsSeparated
      (⟨Sum.inr (i, 0), none, r.rhs.map g.fsStripPushRhsSym⟩ :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  constructor <;> simp_all +decide;
  exact Or.inl fun s hs => by obtain ⟨ n, f, rfl ⟩ := hti s hs; exact Or.inl ⟨ n, rfl ⟩ ;

/-
Helper: lifted rule with no pushes and no consume is flag-separated.
-/
private theorem fsSingleRule_fs_liftedNoPush (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f))
    (hnp : r.rhs.any g.hasPush = false)
    (hc : r.consume = none) :
    IRule.FlagsSeparated
      ({ lhs := Sum.inl r.lhs, consume := r.consume,
         rhs := r.rhs.map g.fsLiftRhsSym } :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  cases hti <;> simp_all +decide [ IRule.FlagsSeparated ];
  · aesop;
  · left; intro s hs; specialize hnp s hs; rcases ‹∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f› s hs with ⟨ n, f, rfl ⟩ ; simp_all +decide [ IndexedGrammar.fsLiftRhsSym ] ;
    cases f <;> tauto

/-
Helper: lifted single-element rule with no consume is flag-separated.
-/
private theorem fsSingleRule_fs_liftedSingle (r : IRule T g.nt g.flag)
    (hti : ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f)
    (hlen : r.rhs.length = 1)
    (hc : r.consume = none) :
    IRule.FlagsSeparated
      ({ lhs := Sum.inl r.lhs, consume := r.consume,
         rhs := r.rhs.map g.fsLiftRhsSym } :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  obtain ⟨s, hs⟩ : ∃ s, r.rhs = [s] := by
    exact List.length_eq_one_iff.mp hlen;
  rcases hti s ( by simp +decide [ hs ] ) with ⟨ n, f, rfl ⟩ ; simp +decide [ hc, hs ];
  cases f <;> simp +decide [ IRule.FlagsSeparated, fsLiftRhsSym ]

/-
Helper: main rule from Case 3c is flag-separated.
-/
private theorem fsSingleRule_fs_mainRule (r : IRule T g.nt g.flag) (i : Nat)
    (hti : ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) :
    IRule.FlagsSeparated
      (⟨Sum.inl r.lhs, none,
        (r.rhs.zipIdx).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s⟩ :
        IRule T (g.nt ⊕ (Nat × Nat)) g.flag) := by
  constructor <;> norm_num +zetaDelta at *;
  left; intro s x j hj hs; rcases hti x (by
  rw [ List.mem_iff_get ] at hj; aesop;) with ⟨n, f, rfl⟩; rcases f with ( _ | f ) <;> simp [fsReplaceRhsSym] at hs ⊢;
  · exact Or.inl ⟨ n, hs.symm ⟩;
  · exact Or.inr ⟨ i, j, hs.symm ⟩

set_option maxHeartbeats 400000 in
theorem fsSingleRule_flagsSeparated (i : Nat) (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f))
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    IRule.FlagsSeparated r' := by
  by_cases hc : r.consume.isSome;
  · by_cases hnp : r.rhs.any g.hasPush = false;
    · unfold IndexedGrammar.fsSingleRule at hr';
      cases hti <;> simp_all +decide [ IRule.FlagsSeparated ];
      · cases hr' <;> aesop;
      · rcases hr' with ( rfl | rfl ) <;> simp_all +decide;
        exact Or.inl fun s hs => by rcases ‹∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f› s hs with ⟨ n, f, rfl ⟩ ; exact Or.inl ⟨ n, rfl ⟩ ;
    · unfold IndexedGrammar.fsSingleRule at hr';
      simp [hc, hnp] at hr';
      rcases hr' with ( rfl | rfl | ⟨ a, b, hab, hr' ⟩ );
      · exact fsSingleRule_fs_consumeRule g r i hc;
      · apply fsSingleRule_fs_intermediateRule;
        grind +locals;
      · cases a ; aesop;
        cases ‹Option g.flag› <;> simp_all +decide [ IRule.FlagsSeparated ];
        aesop;
  · by_cases hnp : r.rhs.any g.hasPush = false;
    · unfold IndexedGrammar.fsSingleRule at hr';
      simp [hc, hnp] at hr';
      convert fsSingleRule_fs_liftedNoPush g r _ _ _;
      · exact hti;
      · exact hnp;
      · cases h : r.consume <;> aesop;
    · by_cases hlen : r.rhs.length = 1;
      · cases hti <;> simp_all +decide;
        · unfold IndexedGrammar.hasPush at hnp; aesop;
        · unfold fsSingleRule at hr';
          rw [ List.length_eq_one_iff ] at hlen;
          rcases hlen with ⟨ a, ha ⟩ ; simp_all +decide [ IRule.FlagsSeparated ] ;
          rcases ‹∃ n f, a = IRhsSymbol.nonterminal n f› with ⟨ n, f, rfl ⟩ ; unfold IndexedGrammar.hasPush at hnp; aesop;
      · have hx : r' ∈ (⟨Sum.inl r.lhs, none, (r.rhs.zipIdx).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s⟩ :: (r.rhs.zipIdx).filterMap fun ⟨s, j⟩ =>
          match s with
          | .nonterminal n (some f) =>
            some ⟨Sum.inr (i, j), (none : Option g.flag),
                  [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩
          | _ => none) := by
            unfold IndexedGrammar.fsSingleRule at hr'; aesop;
        rw [ List.mem_cons ] at hx;
        rcases hx with ( rfl | hx );
        · apply fsSingleRule_fs_mainRule;
          exact hti.resolve_left fun ⟨ a, ha ⟩ => hnp <| by simp +decide [ ha, IndexedGrammar.hasPush ] ;
        · grind +suggestions

theorem flagSeparate_flagsSeparated (hti : g.TerminalsIsolated) :
    (g.flagSeparate).FlagsSeparated := by
  intro r hr;
  unfold flagSeparate at hr;
  rw [ List.mem_flatten ] at hr;
  obtain ⟨ l, hl₁, hl₂ ⟩ := hr;
  rw [ List.mem_map ] at hl₁;
  obtain ⟨ ⟨ r, i ⟩, hr₁, rfl ⟩ := hl₁;
  exact fsSingleRule_flagsSeparated g i r ( hti r ( by rw [ List.mem_iff_get ] at hr₁; aesop ) ) _ hl₂

private theorem fst_mem_of_mem_zipIdx {α : Type} {x : α} {i k : Nat} {xs : List α}
    (h : (x, i) ∈ xs.zipIdx k) : x ∈ xs := by
  have hz := List.mem_zipIdx h
  rcases hz with ⟨hk, hi, hx⟩
  rw [hx]
  exact List.getElem_mem (l := xs) (n := i - k) (by omega)

private theorem getElem?_of_mem_zipIdx {α : Type} {x : α} {i : Nat} {xs : List α}
    (h : (x, i) ∈ xs.zipIdx) : xs[i]? = some x := by
  have hz := List.mem_zipIdx h
  rcases hz with ⟨hk, hi, hx⟩
  have hi' : i < xs.length := by omega
  rw [List.getElem?_eq_getElem hi']
  rw [hx]
  rfl

private theorem fsLiftRhsSym_ne_start (r : IRule T g.nt g.flag)
    (hfresh : ∀ s ∈ r.rhs,
      match s with
      | .nonterminal n _ => n ≠ g.initial
      | .terminal _ => True)
    {s : IRhsSymbol T g.nt g.flag} (hs : s ∈ r.rhs) (f : Option g.flag) :
    g.fsLiftRhsSym s ≠ IRhsSymbol.nonterminal (Sum.inl g.initial) f := by
  cases s with
  | terminal t =>
      intro h
      simp [fsLiftRhsSym] at h
  | nonterminal n f₀ =>
      intro h
      simp [fsLiftRhsSym] at h
      exact hfresh (.nonterminal n f₀) hs h.1

private theorem fsStripPushRhsSym_ne_start (r : IRule T g.nt g.flag)
    (hfresh : ∀ s ∈ r.rhs,
      match s with
      | .nonterminal n _ => n ≠ g.initial
      | .terminal _ => True)
    {s : IRhsSymbol T g.nt g.flag} (hs : s ∈ r.rhs) (f : Option g.flag) :
    g.fsStripPushRhsSym s ≠ IRhsSymbol.nonterminal (Sum.inl g.initial) f := by
  cases s with
  | terminal t =>
      intro h
      simp [fsStripPushRhsSym] at h
  | nonterminal n f₀ =>
      intro h
      simp [fsStripPushRhsSym] at h
      exact hfresh (.nonterminal n f₀) hs h.1

private theorem fsReplaceRhsSym_ne_start (r : IRule T g.nt g.flag)
    (hfresh : ∀ s ∈ r.rhs,
      match s with
      | .nonterminal n _ => n ≠ g.initial
      | .terminal _ => True)
    {s : IRhsSymbol T g.nt g.flag} (hs : s ∈ r.rhs) (i j : Nat) (f : Option g.flag) :
    g.fsReplaceRhsSym i j s ≠ IRhsSymbol.nonterminal (Sum.inl g.initial) f := by
  cases s with
  | terminal t =>
      intro h
      simp [fsReplaceRhsSym] at h
  | nonterminal n f₀ =>
      cases f₀ with
      | none =>
          intro h
          simp [fsReplaceRhsSym] at h
          exact hfresh (.nonterminal n none) hs h.1
      | some a =>
          intro h
          simp [fsReplaceRhsSym] at h

private theorem start_nonterminal_not_mem_zipIdx (r : IRule T g.nt g.flag)
    (hfresh : ∀ s ∈ r.rhs,
      match s with
      | .nonterminal n _ => n ≠ g.initial
      | .terminal _ => True)
    (f : Option g.flag) (j : Nat) :
    (IRhsSymbol.nonterminal g.initial f, j) ∉ r.rhs.zipIdx := by
  intro h
  exact hfresh (.nonterminal g.initial f) (fst_mem_of_mem_zipIdx h) rfl

set_option maxHeartbeats 800000 in
theorem fsSingleRule_startNotOnRhs (i : Nat) (r : IRule T g.nt g.flag)
    (hfresh : ∀ s ∈ r.rhs,
      match s with
      | .nonterminal n _ => n ≠ g.initial
      | .terminal _ => True)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    ∀ s ∈ r'.rhs,
      match s with
      | .nonterminal n _ => n ≠ Sum.inl g.initial
      | .terminal _ => True := by
  have hzip_mem :
      ∀ {s : IRhsSymbol T g.nt g.flag} {j : Nat},
        (s, j) ∈ r.rhs.zipIdx → s ∈ r.rhs :=
    fun {_} {_} h => fst_mem_of_mem_zipIdx h
  unfold IndexedGrammar.fsSingleRule at hr'
  aesop (config := { warnOnNonterminal := false })
    (add safe [fsLiftRhsSym_ne_start, fsStripPushRhsSym_ne_start,
      fsReplaceRhsSym_ne_start, start_nonterminal_not_mem_zipIdx])
  all_goals
    solve_by_elim [fsLiftRhsSym_ne_start, fsStripPushRhsSym_ne_start,
      fsReplaceRhsSym_ne_start, start_nonterminal_not_mem_zipIdx, hzip_mem]

theorem flagSeparate_startNotOnRhs (hfresh : g.StartNotOnRhs') :
    (g.flagSeparate).StartNotOnRhs' := by
  unfold IndexedGrammar.StartNotOnRhs'
  intro r' hr' s hs
  unfold flagSeparate at hr'
  rw [List.mem_flatten] at hr'
  obtain ⟨l, hl₁, hl₂⟩ := hr'
  rw [List.mem_map] at hl₁
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := hl₁
  have hr_mem : r ∈ g.rules := fst_mem_of_mem_zipIdx hri
  rcases s with t | ⟨n, f⟩
  · trivial
  · change n ≠ Sum.inl g.initial
    exact fsSingleRule_startNotOnRhs g i r (hfresh r hr_mem) r' hl₂
      (.nonterminal n f) hs

/-
Lifting expandRhs commutes with fsLiftISym.
-/
theorem fsLiftISym_expandRhs (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (expandRhs g rhs σ).map g.fsLiftISym = expandRhs g.flagSeparate (rhs.map g.fsLiftRhsSym) σ := by
  unfold expandRhs;
  induction rhs <;> aesop

/-
Lifting a list of ISym with map preserves append.
-/
theorem fsLiftISym_map_terminal (w : List T) :
    (w.map (ISym.terminal (g := g))).map g.fsLiftISym = w.map (ISym.terminal (g := g.flagSeparate)) := by
  induction w <;> simp +decide [ * ];
  rfl

/-
A rule r at index i in g.rules gives rules in g.flagSeparate.rules.
-/
theorem fsSingleRule_mem_flagSeparate {r : IRule T g.nt g.flag} {i : Nat}
    (hr : (r, i) ∈ g.rules.zipIdx)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    r' ∈ g.flagSeparate.rules := by
  unfold IndexedGrammar.flagSeparate; aesop;

private theorem map_fsLiftRhsSym_zipIdx
    (rhs : List (IRhsSymbol T g.nt g.flag)) (start : Nat) :
    rhs.map g.fsLiftRhsSym =
      (rhs.zipIdx start).map (fun x => g.fsLiftRhsSym x.1) := by
  induction rhs generalizing start with
  | nil => simp
  | cons s rhs ih =>
      rw [List.zipIdx_cons]
      simp [ih (start + 1)]

/-- Expanding with fsReplaceRhsSym derives to expanding with fsLiftRhsSym via push rules. -/
private theorem resolveIntermediatesPairs
    (l : List (IRhsSymbol T g.nt g.flag × Nat)) (i offset : Nat)
    (hri : ∀ (s : IRhsSymbol T g.nt g.flag) (j : Nat),
      (s, j) ∈ l → g.hasPush s →
      ⟨Sum.inr (i, j + offset), (none : Option g.flag),
        [match s with | .nonterminal n (some f) => IRhsSymbol.nonterminal (Sum.inl n) (some f)
                      | _ => IRhsSymbol.nonterminal (Sum.inl g.initial) none]⟩ ∈ g.flagSeparate.rules)
    (σ : List g.flag) :
    g.flagSeparate.Derives
      (expandRhs g.flagSeparate (l.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + offset) s) σ)
      (expandRhs g.flagSeparate (l.map fun ⟨s, _⟩ => g.fsLiftRhsSym s) σ) := by
  induction' l with x xs ih
  · exact deri_self _ _
  · rcases x with ⟨s, j⟩
    have h_head :
        g.flagSeparate.Derives
          (expandRhs g.flagSeparate [g.fsReplaceRhsSym i (j + offset) s] σ)
          (expandRhs g.flagSeparate [g.fsLiftRhsSym s] σ) := by
      cases s with
      | terminal t =>
          exact deri_self _ _
      | nonterminal n f =>
          cases f with
          | none =>
              exact deri_self _ _
          | some f =>
              apply deri_of_tran
              refine ⟨
                ⟨Sum.inr (i, j + offset), none,
                  [IRhsSymbol.nonterminal (Sum.inl n) (some f)]⟩,
                [], [], σ, ?_, rfl, ?_⟩
              · simpa [hasPush] using hri (.nonterminal n (some f)) j
                  (by simp) (by simp [hasPush])
              · simp [expandRhs, fsLiftRhsSym]
    have h_tail :
        g.flagSeparate.Derives
          (expandRhs g.flagSeparate (xs.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + offset) s) σ)
          (expandRhs g.flagSeparate (xs.map fun ⟨s, _⟩ => g.fsLiftRhsSym s) σ) := by
      apply ih
      intro s k hmem hpush
      exact hri s k (by simp [hmem]) hpush
    have h₁ := deri_with_suffix
      (expandRhs g.flagSeparate (xs.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + offset) s) σ)
      h_head
    have h₂ := deri_with_prefix
      (expandRhs g.flagSeparate [g.fsLiftRhsSym s] σ)
      h_tail
    exact h₁.trans h₂

theorem resolveIntermediates (rhs : List (IRhsSymbol T g.nt g.flag)) (i offset : Nat)
    (hri : ∀ (s : IRhsSymbol T g.nt g.flag) (j : Nat),
      (s, j) ∈ rhs.zipIdx → g.hasPush s →
      ⟨Sum.inr (i, j + offset), (none : Option g.flag),
        [match s with | .nonterminal n (some f) => IRhsSymbol.nonterminal (Sum.inl n) (some f)
                      | _ => IRhsSymbol.nonterminal (Sum.inl g.initial) none]⟩ ∈ g.flagSeparate.rules)
    (σ : List g.flag) :
    g.flagSeparate.Derives
      (expandRhs g.flagSeparate (rhs.zipIdx.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + offset) s) σ)
      (expandRhs g.flagSeparate (rhs.map g.fsLiftRhsSym) σ) := by
  have h := resolveIntermediatesPairs g rhs.zipIdx i offset hri σ
  have hmap :
      rhs.map g.fsLiftRhsSym =
        rhs.zipIdx.map (fun x => g.fsLiftRhsSym x.1) := by
    simpa using map_fsLiftRhsSym_zipIdx g rhs 0
  simpa [hmap] using h

/-- When hasPush is false, fsStripPushRhsSym agrees with fsLiftRhsSym on the list. -/
theorem fsStripPushRhsSym_eq_fsLiftRhsSym_of_noPush
    (rhs : List (IRhsSymbol T g.nt g.flag))
    (hnp : rhs.any g.hasPush = false) :
    rhs.map g.fsStripPushRhsSym = rhs.map g.fsLiftRhsSym := by
  induction' rhs with s rhs ih
  · rfl
  · simp only [List.any_cons] at hnp
    have hs_false : g.hasPush s = false := by
      cases hs : g.hasPush s <;> simp [hs] at hnp ⊢
    have hrest_all : ∀ x ∈ rhs, g.hasPush x = false := by
      cases hs : g.hasPush s
      · simpa [hs] using hnp
      · simp [hs] at hnp
    have hrest : rhs.any g.hasPush = false := by
      rw [List.any_eq_false]
      intro x hx htrue
      rw [hrest_all x hx] at htrue
      contradiction
    simp [ih hrest]
    cases s with
    | terminal t => simp [fsStripPushRhsSym, fsLiftRhsSym]
    | nonterminal n f =>
        cases f with
        | none => simp [fsStripPushRhsSym, fsLiftRhsSym]
        | some f => simp [hasPush] at hs_false

/-- Simulation of a single rule: from the nonterminal with appropriate stack,
    flagSeparate can derive the lifted expansion. -/
theorem fsLift_rule_simulation (r : IRule T g.nt g.flag) (i : Nat)
    (hri : (r, i) ∈ g.rules.zipIdx) (σ : List g.flag) :
    g.flagSeparate.Derives
      [ISym.indexed (g := g.flagSeparate) (Sum.inl r.lhs)
        (match r.consume with | none => σ | some f => f :: σ)]
      (expandRhs g.flagSeparate (r.rhs.map g.fsLiftRhsSym) σ) := by
  rcases r with ⟨lhs, consume, rhs⟩
  let rule_mem :
      ∀ r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag,
        r' ∈ g.fsSingleRule i ⟨lhs, consume, rhs⟩ → r' ∈ g.flagSeparate.rules :=
    fun r' hr' => fsSingleRule_mem_flagSeparate g hri r' hr'
  by_cases hc : consume.isSome
  · rcases Option.isSome_iff_exists.mp hc with ⟨f, hconsume⟩
    subst consume
    by_cases hpushFalse : rhs.any g.hasPush = false
    · have h₁ :
          g.flagSeparate.Derives
            [ISym.indexed (g := g.flagSeparate) (Sum.inl lhs) (f :: σ)]
            [ISym.indexed (g := g.flagSeparate) (Sum.inr (i, 0)) σ] := by
        apply deri_of_tran
        refine ⟨⟨Sum.inl lhs, some f,
            [IRhsSymbol.nonterminal (Sum.inr (i, 0)) none]⟩,
          [], [], σ, ?_, rfl, ?_⟩
        · apply rule_mem
          unfold fsSingleRule
          simp [hpushFalse]
        · simp [expandRhs]
      have h₂ :
          g.flagSeparate.Derives
            [ISym.indexed (g := g.flagSeparate) (Sum.inr (i, 0)) σ]
            (expandRhs g.flagSeparate (rhs.map g.fsStripPushRhsSym) σ) := by
        apply deri_of_tran
        refine ⟨⟨Sum.inr (i, 0), none, rhs.map g.fsStripPushRhsSym⟩,
          [], [], σ, ?_, rfl, ?_⟩
        · apply rule_mem
          unfold fsSingleRule
          simp [hpushFalse]
        · simp
      have hstrip := fsStripPushRhsSym_eq_fsLiftRhsSym_of_noPush g rhs hpushFalse
      simpa [hstrip] using h₁.trans h₂
    · have hpushTrue : rhs.any g.hasPush = true := by
        cases h : rhs.any g.hasPush <;> simp [h] at hpushFalse ⊢
      have h₁ :
          g.flagSeparate.Derives
            [ISym.indexed (g := g.flagSeparate) (Sum.inl lhs) (f :: σ)]
            [ISym.indexed (g := g.flagSeparate) (Sum.inr (i, 0)) σ] := by
        apply deri_of_tran
        refine ⟨⟨Sum.inl lhs, some f,
            [IRhsSymbol.nonterminal (Sum.inr (i, 0)) none]⟩,
          [], [], σ, ?_, rfl, ?_⟩
        · apply rule_mem
          unfold fsSingleRule
          simp [hpushTrue]
        · simp [expandRhs]
      have h₂ :
          g.flagSeparate.Derives
            [ISym.indexed (g := g.flagSeparate) (Sum.inr (i, 0)) σ]
            (expandRhs g.flagSeparate
              (rhs.zipIdx.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s) σ) := by
        apply deri_of_tran
        refine ⟨⟨Sum.inr (i, 0), none,
            rhs.zipIdx.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s⟩,
          [], [], σ, ?_, rfl, ?_⟩
        · apply rule_mem
          unfold fsSingleRule
          simp [hpushTrue]
        · simp
      have hpushRules :
          ∀ (s : IRhsSymbol T g.nt g.flag) (j : Nat),
            (s, j) ∈ rhs.zipIdx → g.hasPush s →
            ⟨Sum.inr (i, j + 1), (none : Option g.flag),
              [match s with
                | .nonterminal n (some f) => IRhsSymbol.nonterminal (Sum.inl n) (some f)
                | _ => IRhsSymbol.nonterminal (Sum.inl g.initial) none]⟩ ∈
              g.flagSeparate.rules := by
        intro s j hmem hpush
        cases s with
        | terminal t => simp [hasPush] at hpush
        | nonterminal n fopt =>
            cases fopt with
            | none => simp [hasPush] at hpush
            | some fp =>
                apply rule_mem
                unfold fsSingleRule
                simp [hpushTrue]
                right
                exact ⟨IRhsSymbol.nonterminal n (some fp), j, hmem, rfl⟩
      exact h₁.trans (h₂.trans (resolveIntermediates g rhs i 1 hpushRules σ))
  · have hconsume : consume = none := by
      cases consume <;> simp_all
    subst consume
    by_cases hpushFalse : rhs.any g.hasPush = false
    · apply deri_of_tran
      refine ⟨⟨Sum.inl lhs, none, rhs.map g.fsLiftRhsSym⟩,
        [], [], σ, ?_, rfl, ?_⟩
      · apply rule_mem
        unfold fsSingleRule
        simp [hpushFalse]
      · simp
    · have hpushTrue : rhs.any g.hasPush = true := by
        cases h : rhs.any g.hasPush <;> simp [h] at hpushFalse ⊢
      by_cases hlen : rhs.length == 1
      · apply deri_of_tran
        refine ⟨⟨Sum.inl lhs, none, rhs.map g.fsLiftRhsSym⟩,
          [], [], σ, ?_, rfl, ?_⟩
        · apply rule_mem
          unfold fsSingleRule
          simp [hpushTrue, hlen]
        · simp
      · have h₁ :
            g.flagSeparate.Derives
              [ISym.indexed (g := g.flagSeparate) (Sum.inl lhs) σ]
              (expandRhs g.flagSeparate
                (rhs.zipIdx.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s) σ) := by
          apply deri_of_tran
          refine ⟨⟨Sum.inl lhs, none,
              rhs.zipIdx.map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s⟩,
            [], [], σ, ?_, rfl, ?_⟩
          · apply rule_mem
            unfold fsSingleRule
            simp [hpushTrue, hlen]
          · simp
        have hpushRules :
            ∀ (s : IRhsSymbol T g.nt g.flag) (j : Nat),
              (s, j) ∈ rhs.zipIdx → g.hasPush s →
              ⟨Sum.inr (i, j + 0), (none : Option g.flag),
                [match s with
                  | .nonterminal n (some f) => IRhsSymbol.nonterminal (Sum.inl n) (some f)
                  | _ => IRhsSymbol.nonterminal (Sum.inl g.initial) none]⟩ ∈
                g.flagSeparate.rules := by
          intro s j hmem hpush
          cases s with
          | terminal t => simp [hasPush] at hpush
          | nonterminal n fopt =>
              cases fopt with
              | none => simp [hasPush] at hpush
              | some fp =>
                  apply rule_mem
                  unfold fsSingleRule
                  simp [hpushTrue, hlen]
                  exact ⟨IRhsSymbol.nonterminal n (some fp), j, hmem, rfl⟩
        exact h₁.trans (resolveIntermediates g rhs i 0 hpushRules σ)

/-
Each single transform step in g can be simulated by one or more steps in flagSeparate.
-/
theorem fsLift_transforms {u v : List g.ISym}
    (h : g.Transforms u v) :
    g.flagSeparate.Derives (u.map g.fsLiftISym) (v.map g.fsLiftISym) := by
  obtain ⟨ r, u_prefix, v_suffix, σ, hr, hu, hv ⟩ := h;
  -- Apply the simulation result to get the derivation in the flag-separated grammar.
  have h_sim : g.flagSeparate.Derives
    [ISym.indexed (g := g.flagSeparate) (Sum.inl r.lhs) (match r.consume with | none => σ | some f => f :: σ)]
    (expandRhs g.flagSeparate (r.rhs.map g.fsLiftRhsSym) σ) := by
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr;
      convert fsLift_rule_simulation g r i _ σ;
      grind +qlia;
  convert deri_with_prefix ( u_prefix.map g.fsLiftISym ) ( deri_with_suffix ( v_suffix.map g.fsLiftISym ) h_sim ) using 1;
  · aesop;
  · rw [hv];
    simp +decide [ ← List.append_assoc, fsLiftISym_expandRhs ]

/-
If g derives u from v, then flagSeparate derives the lifted versions.
-/
theorem fsLift_derives {u v : List g.ISym}
    (h : g.Derives u v) :
    g.flagSeparate.Derives (u.map g.fsLiftISym) (v.map g.fsLiftISym) := by
  have h_lift_transform : ∀ {w₁ w₂ : List g.ISym}, g.Transforms w₁ w₂ → g.flagSeparate.Derives (w₁.map g.fsLiftISym) (w₂.map g.fsLiftISym) := by
    exact fun {w₁ w₂} a => fsLift_transforms g a
  induction h;
  · exact deri_self g.flagSeparate (map g.fsLiftISym u)
  · rename_i h₁ h₂ ih
    exact deri_of_deri_deri ih (h_lift_transform h₂)

theorem flagSeparate_language_forward {w : List T}
    (h : g.Generates w) : (g.flagSeparate).Generates w := by
  unfold IndexedGrammar.Generates at *;
  convert fsLift_derives _ _;
  case convert_3 => exact [ ISym.indexed g.initial [] ];
  all_goals norm_cast;
  exact Eq.symm (fsLiftISym_map_terminal g w)

noncomputable def fsUnsepIntermediate (idx : Nat × Nat) (σ : List g.flag) : List g.ISym :=
  match g.rules[idx.1]? with
  | none => []
  | some r =>
      if r.consume.isSome ∧ idx.2 = 0 then
        expandRhs g r.rhs σ
      else
        let pos := if r.consume.isSome then idx.2 - 1 else idx.2
        match r.rhs[pos]? with
        | none => []
        | some (.terminal t) => [.terminal t]
        | some (.nonterminal n none) => [.indexed n σ]
        | some (.nonterminal n (some f)) => [.indexed n (f :: σ)]

noncomputable def fsUnsepSym : (g.flagSeparate).ISym → List g.ISym
  | .terminal t => [.terminal t]
  | .indexed (Sum.inl n) σ => [.indexed n σ]
  | .indexed (Sum.inr idx) σ => g.fsUnsepIntermediate idx σ

noncomputable def fsUnsepSF (w : List (g.flagSeparate).ISym) : List g.ISym :=
  w.flatMap g.fsUnsepSym

private theorem fsUnsepSF_append (u v : List (g.flagSeparate).ISym) :
    g.fsUnsepSF (u ++ v) = g.fsUnsepSF u ++ g.fsUnsepSF v := by
  unfold fsUnsepSF
  simp [List.flatMap_append]

private theorem fsUnsepSF_terminal (w : List T) :
    g.fsUnsepSF (w.map (ISym.terminal (g := g.flagSeparate))) =
      w.map (ISym.terminal (g := g)) := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      simp [fsUnsepSF, fsUnsepSym] at ih ⊢
      exact ih

private theorem fsUnsep_original_step (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) (σ : List g.flag) :
    g.Derives
      (match r.consume with
       | none => [ISym.indexed r.lhs σ]
       | some f => [ISym.indexed r.lhs (f :: σ)])
      (expandRhs g r.rhs σ) := by
  apply deri_of_tran
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · cases r.consume <;> rfl
  · simp

private theorem flagSeparate_rule_origin
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.flagSeparate.rules) :
    ∃ (i : Nat) (r : IRule T g.nt g.flag),
      (r, i) ∈ g.rules.zipIdx ∧ r' ∈ g.fsSingleRule i r := by
  unfold flagSeparate at hr'
  rw [List.mem_flatten] at hr'
  obtain ⟨l, hl₁, hl₂⟩ := hr'
  rw [List.mem_map] at hl₁
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := hl₁
  exact ⟨i, r, hri, hl₂⟩

private theorem fsUnsepSF_expand_lift
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    g.fsUnsepSF (expandRhs g.flagSeparate (rhs.map g.fsLiftRhsSym) σ) =
      expandRhs g rhs σ := by
  induction rhs with
  | nil => rfl
  | cons s rhs ih =>
      cases s with
      | terminal t =>
          simp [fsUnsepSF, fsUnsepSym, fsLiftRhsSym, expandRhs] at ih ⊢
          exact ih
      | nonterminal n f =>
          cases f <;> simp [fsUnsepSF, fsUnsepSym, fsLiftRhsSym, expandRhs] at ih ⊢
          · exact ih
          · exact ih

private theorem fsUnsepSym_inr_zero (i : Nat) (r : IRule T g.nt g.flag)
    (hri : (r, i) ∈ g.rules.zipIdx) (hc : r.consume.isSome = true)
    (σ : List g.flag) :
    g.fsUnsepSym (.indexed (Sum.inr (i, 0)) σ) = expandRhs g r.rhs σ := by
  have hi := getElem?_of_mem_zipIdx hri
  simp [fsUnsepSym, fsUnsepIntermediate, hi, hc]

private theorem fsUnsepSym_inr_push_consume
    (i j : Nat) (r : IRule T g.nt g.flag) (hri : (r, i) ∈ g.rules.zipIdx)
    (hc : r.consume.isSome = true) (n : g.nt) (f : g.flag)
    (hmem : (IRhsSymbol.nonterminal n (some f), j) ∈ r.rhs.zipIdx)
    (σ : List g.flag) :
    g.fsUnsepSym (.indexed (Sum.inr (i, j + 1)) σ) = [ISym.indexed n (f :: σ)] := by
  have hi := getElem?_of_mem_zipIdx hri
  have hs := getElem?_of_mem_zipIdx hmem
  simp [fsUnsepSym, fsUnsepIntermediate, hi, hc, hs]

private theorem fsUnsepSym_inr_push_noConsume
    (i j : Nat) (r : IRule T g.nt g.flag) (hri : (r, i) ∈ g.rules.zipIdx)
    (hc : r.consume = none) (n : g.nt) (f : g.flag)
    (hmem : (IRhsSymbol.nonterminal n (some f), j) ∈ r.rhs.zipIdx)
    (σ : List g.flag) :
    g.fsUnsepSym (.indexed (Sum.inr (i, j)) σ) = [ISym.indexed n (f :: σ)] := by
  have hi := getElem?_of_mem_zipIdx hri
  have hs := getElem?_of_mem_zipIdx hmem
  simp [fsUnsepSym, fsUnsepIntermediate, hi, hc, hs]

private theorem fsUnsepSF_expand_strip_noPush
    (rhs : List (IRhsSymbol T g.nt g.flag))
    (hnp : ∀ x ∈ rhs, g.hasPush x = false) (σ : List g.flag) :
    g.fsUnsepSF (expandRhs g.flagSeparate (rhs.map g.fsStripPushRhsSym) σ) =
      expandRhs g rhs σ := by
  induction rhs with
  | nil => rfl
  | cons s rhs ih =>
      have hs : g.hasPush s = false := hnp s (by simp)
      have hrest : ∀ x ∈ rhs, g.hasPush x = false := by
        intro x hx
        exact hnp x (by simp [hx])
      cases s with
      | terminal t =>
          simp [fsUnsepSF, fsUnsepSym, fsStripPushRhsSym, expandRhs] at ih ⊢
          exact ih hrest
      | nonterminal n f =>
          cases f with
          | none =>
              simp [fsUnsepSF, fsUnsepSym, fsStripPushRhsSym, expandRhs] at ih ⊢
              exact ih hrest
          | some f =>
              simp [hasPush] at hs

private theorem fsUnsepSF_expand_replace_consume
    (i start : Nat) (r : IRule T g.nt g.flag)
    (hi : g.rules[i]? = some r) (hc : r.consume.isSome = true)
    (rhs : List (IRhsSymbol T g.nt g.flag))
    (hget : ∀ s j, (s, j) ∈ rhs.zipIdx start → r.rhs[j]? = some s)
    (σ : List g.flag) :
    g.fsUnsepSF
        (expandRhs g.flagSeparate
          ((rhs.zipIdx start).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i (j + 1) s) σ) =
      expandRhs g rhs σ := by
  induction rhs generalizing start with
  | nil => rfl
  | cons s rhs ih =>
      have hhead : r.rhs[start]? = some s := by
        apply hget
        simp [List.zipIdx_cons]
      have htail :
          ∀ s j, (s, j) ∈ rhs.zipIdx (start + 1) → r.rhs[j]? = some s := by
        intro s j hmem
        exact hget s j (by simp [List.zipIdx_cons, hmem])
      have iht := ih (start + 1) htail
      simp [fsUnsepSF, expandRhs] at iht
      cases s with
      | terminal t =>
          simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym, expandRhs]
          exact iht
      | nonterminal n f =>
          cases f with
          | none =>
              simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym, expandRhs]
              exact iht
          | some f =>
              simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym,
                fsUnsepIntermediate, expandRhs, hi, hc, hhead]
              exact iht

private theorem fsUnsepSF_expand_replace_noConsume
    (i start : Nat) (r : IRule T g.nt g.flag)
    (hi : g.rules[i]? = some r) (hc : r.consume = none)
    (rhs : List (IRhsSymbol T g.nt g.flag))
    (hget : ∀ s j, (s, j) ∈ rhs.zipIdx start → r.rhs[j]? = some s)
    (σ : List g.flag) :
    g.fsUnsepSF
        (expandRhs g.flagSeparate
          ((rhs.zipIdx start).map fun ⟨s, j⟩ => g.fsReplaceRhsSym i j s) σ) =
      expandRhs g rhs σ := by
  induction rhs generalizing start with
  | nil => rfl
  | cons s rhs ih =>
      have hhead : r.rhs[start]? = some s := by
        apply hget
        simp [List.zipIdx_cons]
      have htail :
          ∀ s j, (s, j) ∈ rhs.zipIdx (start + 1) → r.rhs[j]? = some s := by
        intro s j hmem
        exact hget s j (by simp [List.zipIdx_cons, hmem])
      have iht := ih (start + 1) htail
      simp [fsUnsepSF, expandRhs] at iht
      cases s with
      | terminal t =>
          simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym, expandRhs]
          exact iht
      | nonterminal n f =>
          cases f with
          | none =>
              simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym, expandRhs]
              exact iht
          | some f =>
              simp [List.zipIdx_cons, fsUnsepSF, fsUnsepSym, fsReplaceRhsSym,
                fsUnsepIntermediate, expandRhs, hi, hc, hhead]
              exact iht

set_option maxHeartbeats 800000 in
private theorem fsUnsep_rule_step_of
    (i : Nat) (r : IRule T g.nt g.flag) (hri : (r, i) ∈ g.rules.zipIdx)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) (σ : List g.flag) :
    g.Derives
      (g.fsUnsepSym (match r'.consume with
        | none => .indexed r'.lhs σ
        | some f => .indexed r'.lhs (f :: σ)))
      (g.fsUnsepSF (expandRhs g.flagSeparate r'.rhs σ)) := by
  have hr_mem : r ∈ g.rules := fst_mem_of_mem_zipIdx hri
  unfold IndexedGrammar.fsSingleRule at hr'
  aesop (config := { warnOnNonterminal := false })
  all_goals
    first
    | have hi := getElem?_of_mem_zipIdx hri
      have hright := fsUnsepSF_expand_replace_consume g i 0 r hi h r.rhs
        (by intro s j hmem; exact getElem?_of_mem_zipIdx hmem) σ
      have hleft := fsUnsepSym_inr_zero g i r hri h σ
      rw [hleft, hright]
      exact deri_self g _
    | have hleft := fsUnsepSym_inr_zero g i r hri h σ
      have hright := fsUnsepSF_expand_strip_noPush g r.rhs h_1 σ
      rw [hleft, hright]
      exact deri_self g _
    | rw [fsUnsepSF_expand_lift]
      simpa [fsUnsepSym, h] using fsUnsep_original_step g r hr_mem σ
    | have hi := getElem?_of_mem_zipIdx hri
      have hright := fsUnsepSF_expand_replace_noConsume g i 0 r hi h r.rhs
        (by intro s j hmem; exact getElem?_of_mem_zipIdx hmem) σ
      rw [hright]
      simpa [fsUnsepSym, h] using fsUnsep_original_step g r hr_mem σ
    | have hleft := fsUnsepSym_inr_push_consume g i w_2 r hri h a val left_1 σ
      rw [hleft]
      simp [fsUnsepSF, fsUnsepSym, expandRhs]
      exact deri_self g _
    | have hleft := fsUnsepSym_inr_push_noConsume g i w_2 r hri h a val left_1 σ
      rw [hleft]
      simp [fsUnsepSF, fsUnsepSym, expandRhs]
      exact deri_self g _
    | have hc : r.consume.isSome = true := by simp [heq]
      have hright := fsUnsepSym_inr_zero g i r hri hc σ
      simp [fsUnsepSF, expandRhs]
      rw [hright]
      simpa [fsUnsepSym, heq] using fsUnsep_original_step g r hr_mem σ

private theorem fsUnsep_transforms {u v : List (g.flagSeparate).ISym}
    (h : g.flagSeparate.Transforms u v) :
    g.Derives (g.fsUnsepSF u) (g.fsUnsepSF v) := by
  obtain ⟨r', u₀, v₀, σ, hr', hu, hv⟩ := h
  obtain ⟨i, r, hri, hr_single⟩ := flagSeparate_rule_origin g r' hr'
  have key := fsUnsep_rule_step_of g i r hri r' hr_single σ
  have hsingle : ∀ s : (g.flagSeparate).ISym,
      g.fsUnsepSF [s] = g.fsUnsepSym s := by
    intro s
    simp [fsUnsepSF]
  cases hc : r'.consume with
  | none =>
      rw [hc] at hu key
      simp only at hu key
      rw [hu, hv]
      simp only [fsUnsepSF_append]
      rw [hsingle (.indexed r'.lhs σ)]
      exact deri_with_suffix _ (deri_with_prefix _ key)
  | some f =>
      rw [hc] at hu key
      simp only at hu key
      rw [hu, hv]
      simp only [fsUnsepSF_append]
      rw [hsingle (.indexed r'.lhs (f :: σ))]
      exact deri_with_suffix _ (deri_with_prefix _ key)

private theorem fsUnsep_derives {u v : List (g.flagSeparate).ISym}
    (h : g.flagSeparate.Derives u v) :
    g.Derives (g.fsUnsepSF u) (g.fsUnsepSF v) := by
  induction h with
  | refl => exact deri_self g _
  | tail _ ht ih =>
      exact ih.trans (fsUnsep_transforms g ht)

theorem flagSeparate_language_backward {w : List T}
    (h : (g.flagSeparate).Generates w) : g.Generates w := by
  unfold IndexedGrammar.Generates at *
  have hd := fsUnsep_derives g h
  rw [fsUnsepSF_terminal g w] at hd
  simpa [fsUnsepSF, fsUnsepSym, flagSeparate] using hd

theorem flagSeparate_generates_iff (w : List T) :
    (g.flagSeparate).Generates w ↔ g.Generates w :=
  ⟨g.flagSeparate_language_backward, g.flagSeparate_language_forward⟩

theorem exists_flagsSeparated_all (g : IndexedGrammar T)
    (hti : g.TerminalsIsolated) :
    ∃ g' : IndexedGrammar T,
      g'.TerminalsIsolated ∧ g'.FlagsSeparated ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, (g'.Generates w ↔ g.Generates w) :=
  ⟨g.flagSeparate, g.flagSeparate_terminalsIsolated hti,
   g.flagSeparate_flagsSeparated hti,
   g.flagSeparate_startNotOnRhs,
   g.flagSeparate_generates_iff⟩

theorem exists_flagsSeparated (g : IndexedGrammar T)
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated) :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧ g'.TerminalsIsolated ∧ g'.FlagsSeparated ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, (g'.Generates w ↔ g.Generates w) :=
  ⟨g.flagSeparate, g.flagSeparate_noEpsilon hne, g.flagSeparate_terminalsIsolated hti,
   g.flagSeparate_flagsSeparated hti,
   g.flagSeparate_startNotOnRhs,
   g.flagSeparate_generates_iff⟩

theorem exists_flagsSeparated' (g : IndexedGrammar T)
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated) :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧ g'.TerminalsIsolated ∧ g'.FlagsSeparated ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  obtain ⟨g', hne', hti', hfs, hfresh, hlang⟩ := g.exists_flagsSeparated hne hti
  exact ⟨g', hne', hti', hfs, hfresh, fun w _ => hlang w⟩

end FlagSeparation

end IndexedGrammar
