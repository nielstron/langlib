import Mathlib
import Langlib.Grammars.Indexed.Definition

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
  split_ifs at hr' <;> simp_all +decide only [List.mem_cons, List.mem_singleton];
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
    · cases hr' <;> simp_all +decide [ List.mem_cons, List.mem_singleton ];
      rename_i k hk₁ hk₂ hk₃;
      cases hk₃;
      · rcases hti with ( ⟨ a, ha ⟩ | hti ) <;> simp_all +decide [ List.map ];
        · exact Or.inl ⟨ a, rfl ⟩;
        · exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := hti s hs; exact Or.inl ⟨ n, none, rfl ⟩ ;
      · contradiction;
  · grind +suggestions;
  · split_ifs at hr';
    · cases hti <;> simp_all +decide [ List.mem_singleton ];
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
  constructor <;> simp_all +decide [ IRule.FlagsSeparated ];
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
      · rcases hr' with ( rfl | rfl ) <;> simp_all +decide [ IRule.FlagsSeparated ];
        exact Or.inl fun s hs => by rcases ‹∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f› s hs with ⟨ n, f, rfl ⟩ ; exact Or.inl ⟨ n, rfl ⟩ ;
    · unfold IndexedGrammar.fsSingleRule at hr';
      simp [hc, hnp] at hr';
      rcases hr' with ( rfl | rfl | ⟨ a, b, hab, hr' ⟩ );
      · exact?;
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

/-- Expanding with fsReplaceRhsSym derives to expanding with fsLiftRhsSym via push rules. -/
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
  sorry

/-- When hasPush is false, fsStripPushRhsSym agrees with fsLiftRhsSym on the list. -/
theorem fsStripPushRhsSym_eq_fsLiftRhsSym_of_noPush
    (rhs : List (IRhsSymbol T g.nt g.flag))
    (hnp : rhs.any g.hasPush = false) :
    rhs.map g.fsStripPushRhsSym = rhs.map g.fsLiftRhsSym := by
  sorry

/-- Simulation of a single rule: from the nonterminal with appropriate stack,
    flagSeparate can derive the lifted expansion. -/
theorem fsLift_rule_simulation (r : IRule T g.nt g.flag) (i : Nat)
    (hri : (r, i) ∈ g.rules.zipIdx) (σ : List g.flag) :
    g.flagSeparate.Derives
      [ISym.indexed (g := g.flagSeparate) (Sum.inl r.lhs)
        (match r.consume with | none => σ | some f => f :: σ)]
      (expandRhs g.flagSeparate (r.rhs.map g.fsLiftRhsSym) σ) := by
  sorry

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
    exact?;
  induction h;
  · exact?;
  · exact?

theorem flagSeparate_language_forward {w : List T}
    (h : g.Generates w) : (g.flagSeparate).Generates w := by
  unfold IndexedGrammar.Generates at *;
  convert fsLift_derives _ _;
  case convert_3 => exact [ ISym.indexed g.initial [] ];
  all_goals norm_cast;
  exact?

theorem flagSeparate_language_backward {w : List T}
    (h : (g.flagSeparate).Generates w) : g.Generates w := by
  sorry

theorem exists_flagsSeparated' (g : IndexedGrammar T)
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated) :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧ g'.TerminalsIsolated ∧ g'.FlagsSeparated ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) :=
  ⟨g.flagSeparate, g.flagSeparate_noEpsilon hne, g.flagSeparate_terminalsIsolated hti,
   g.flagSeparate_flagsSeparated hti,
   fun _ _ => ⟨g.flagSeparate_language_backward, g.flagSeparate_language_forward⟩⟩

end FlagSeparation

end IndexedGrammar