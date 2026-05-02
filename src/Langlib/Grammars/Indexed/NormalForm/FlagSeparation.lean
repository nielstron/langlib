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

/-- Transform a single rule at index `i` into flag-separated rules. -/
def fsSingleRule (i : Nat) (r : IRule T g.nt g.flag) :
    List (IRule T (g.nt ⊕ (Nat × Nat)) g.flag) :=
  -- Case 1: Terminal RHS — keep as-is (lifted)
  if r.rhs.any (fun s => match s with | .terminal _ => true | _ => false) && r.rhs.length == 1 then
    [{ lhs := Sum.inl r.lhs, consume := r.consume, rhs := r.rhs.map g.fsLiftRhsSym }]
  -- Case 2: Consumes a flag
  else if r.consume.isSome then
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
  -- Case 3: No consumption
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
  split_ifs at hr';
  · aesop;
  · by_cases h : r.rhs.any g.hasPush <;> simp +decide [ h ] at hr' ⊢;
    · rcases hr' with ( rfl | rfl | ⟨ a, b, hab, h ⟩ ) <;> norm_num at *;
      · assumption;
      · rcases a with ( _ | ⟨ n, f ⟩ ) <;> norm_num at *;
        · cases h;
        · cases f <;> simp +decide at h ⊢;
          exact h ▸ by simp +decide ;
    · rcases hr' with ( rfl | rfl ) <;> simp +decide [ hr ];
  · cases r' ; aesop;
  · aesop

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
-/
theorem fsSingleRule_terminalsIsolated (i : Nat) (r : IRule T g.nt g.flag)
    (hti : (∃ a : T, r.rhs = [IRhsSymbol.terminal a]) ∨
           (∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f))
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) g.flag)
    (hr' : r' ∈ g.fsSingleRule i r) :
    (∃ a : T, r'.rhs = [IRhsSymbol.terminal a]) ∨
    (∀ s ∈ r'.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f) := by
  unfold fsSingleRule at hr';
  split_ifs at hr';
  · rcases r_rhh : r.rhs with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
    cases x <;> tauto;
  · by_cases h : r.rhs.any g.hasPush <;> simp +decide [ h ] at hr' ⊢;
    · rcases hr' with ( rfl | rfl | ⟨ a, b, hab, hr' ⟩ );
      · exact Or.inr fun s hs => Or.inr ⟨ i, 0, none, by simpa using hs ⟩;
      · right;
        intro s hs;
        rw [ List.mem_map ] at hs;
        rcases hs with ⟨ a, ha, rfl ⟩ ; rcases a with ⟨ a, j ⟩ ; rcases a with ( _ | _ ) <;> simp +decide [ * ] at ha ⊢;
        · contrapose! hti;
          constructor;
          · intro a ha; simp_all +decide ;
          · rw [ List.mem_iff_get ] at ha;
            obtain ⟨ n, hn ⟩ := ha;
            use r.rhs.get ⟨ n, by
              exact n.2.trans_le ( by simp ) ⟩
            generalize_proofs at *;
            grind;
        · unfold fsReplaceRhsSym; aesop;
      · rw [ List.mem_iff_get ] at hab;
        rcases hab with ⟨ n, hn ⟩ ; rcases a with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ List.get ] at hn ⊢;
        · cases hr';
        · cases f <;> simp +decide at hr' ⊢;
          grind +revert;
    · rcases hr' with ( rfl | rfl ) <;> simp +decide [ h ];
      rcases hti with ( ⟨ a, ha ⟩ | hti );
      · grind;
      · exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := hti s hs; exact Or.inl ⟨ n, none, rfl ⟩ ;
  · rcases hti with ( ⟨ a, ha ⟩ | hti ) <;> simp_all +decide;
    exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := hti s hs; exact Or.inl ⟨ n, f, by cases f <;> rfl ⟩ ;
  · by_cases h : r.rhs.any g.hasPush <;> simp +decide [ h ] at hr' ⊢;
    · rcases hr' with ( rfl | ⟨ a, b, hab, hr' ⟩ );
      · right;
        intro s hs;
        rw [ List.mem_map ] at hs;
        rcases hs with ⟨ ⟨ s, j ⟩, hs, rfl ⟩ ; rcases s with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ * ] at hs ⊢;
        · rw [ List.mem_iff_get ] at hs; obtain ⟨ k, hk ⟩ := hs; simp +decide [ List.get ] at hk;
          exact absurd ( hti.resolve_left ( by aesop ) _ ( show r.rhs[k] ∈ r.rhs from by simp ) ) ( by aesop );
        · cases f <;> simp +decide [ fsReplaceRhsSym ];
      · rcases a with ( _ | ⟨ n, f ⟩ );
        · cases hr';
        · cases f <;> simp +decide at hr' ⊢;
          exact Or.inr fun s hs => Or.inl ⟨ n, _, by subst hr'; exact List.mem_singleton.mp hs ⟩;
    ·
      -- Since the original rhs has all nonterminals, the mapped rhs will also have all nonterminals.
      have h_all_nonterminals : ∀ s ∈ r.rhs, ∃ n f, s = IRhsSymbol.nonterminal n f :=
        hti.resolve_left (fun ⟨a, ha⟩ => by simp_all [ha])
      have h_mapped_nonterminals : ∀ s ∈ r.rhs.map g.fsLiftRhsSym, ∃ n f, s = IRhsSymbol.nonterminal n f :=
        fsLiftRhsSym_map_all_nt g r.rhs h_all_nonterminals;
      exact Or.inr fun s hs => by obtain ⟨ n, f, rfl ⟩ := h_mapped_nonterminals s ( by simpa [ hr' ] using hs ) ; cases n <;> [ exact Or.inl ⟨ _, _, rfl ⟩ ; exact Or.inr ⟨ _, _, _, rfl ⟩ ] ;

theorem flagSeparate_terminalsIsolated (hti : g.TerminalsIsolated) :
    (g.flagSeparate).TerminalsIsolated := by
  -- Apply the hypothesis `hti` to the rule `r` in the original grammar.
  intros r' hr'
  obtain ⟨r, hr⟩ := List.mem_flatten.mp hr';
  rcases hr with ⟨ hr₁, hr₂ ⟩;
  rw [ List.mem_map ] at hr₁;
  rcases hr₁ with ⟨ ⟨ r, i ⟩, hr₁, rfl ⟩;
  exact fsSingleRule_terminalsIsolated g i r ( hti r ( by rw [ List.mem_iff_get ] at hr₁; aesop ) ) r' hr₂

theorem flagSeparate_flagsSeparated (hti : g.TerminalsIsolated) :
    (g.flagSeparate).FlagsSeparated := by
  sorry

theorem flagSeparate_language_forward {w : List T}
    (h : g.Generates w) : (g.flagSeparate).Generates w := by
  sorry

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