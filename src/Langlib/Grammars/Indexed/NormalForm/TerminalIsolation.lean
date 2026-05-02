import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # Terminal Isolation for Indexed Grammars

This file constructs a terminal-isolation transformation for indexed grammars.
Given an indexed grammar with no ε-productions, it produces an equivalent grammar
where every rule's RHS is either a single terminal or consists entirely of nonterminals.

This is Step 3 of Aho's Normal Form theorem.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section TerminalIsolation

variable (g : IndexedGrammar T)

/-- Transform an RHS symbol by replacing terminals with fresh nonterminals. -/
def tiLiftRhsSym : IRhsSymbol T g.nt g.flag → IRhsSymbol T (g.nt ⊕ T) g.flag
  | .terminal t => .nonterminal (Sum.inr t) none
  | .nonterminal n f => .nonterminal (Sum.inl n) f

/-- Transform an RHS symbol for the identity embedding (no terminal replacement). -/
def tiEmbedRhsSym : IRhsSymbol T g.nt g.flag → IRhsSymbol T (g.nt ⊕ T) g.flag
  | .terminal t => .terminal t
  | .nonterminal n f => .nonterminal (Sum.inl n) f

/-- Collect all terminals appearing in all rules' RHS. -/
def collectTerminals : List T :=
  (g.rules.map fun r =>
    r.rhs.filterMap fun s =>
      match s with
      | .terminal t => some t
      | .nonterminal _ _ => none).flatten

/-- The terminal-isolation grammar. Every terminal in a rule's RHS is replaced with a
    fresh nonterminal `Sum.inr t`, and for each such terminal a rule `Sum.inr t → t`
    is added. -/
def termIsolate : IndexedGrammar T where
  nt := g.nt ⊕ T
  flag := g.flag
  initial := Sum.inl g.initial
  rules :=
    -- Transformed original rules: replace terminals with nonterminals
    (g.rules.map fun r => {
      lhs := Sum.inl r.lhs
      consume := r.consume
      rhs := r.rhs.map g.tiLiftRhsSym
    }) ++
    -- Terminal rules: Sum.inr t → t
    ((collectTerminals g).map fun t => {
      lhs := Sum.inr t
      consume := (none : Option g.flag)
      rhs := [IRhsSymbol.terminal t]
    })

/-! ### Properties of the construction -/

theorem termIsolate_noEpsilon (hne : g.NoEpsilon') :
    (g.termIsolate).NoEpsilon' := by
  unfold IndexedGrammar.termIsolate;
  intro r hr; aesop;

theorem termIsolate_terminalsIsolated :
    (g.termIsolate).TerminalsIsolated := by
  intro r hr; by_cases h : ∃ t : T, r = { lhs := Sum.inr t, consume := none, rhs := [IRhsSymbol.terminal t] } <;> simp_all +decide [ IndexedGrammar.termIsolate ] ;
  · grind;
  · rcases hr with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ IndexedGrammar.collectTerminals ];
    right; intro s hs; rcases s with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ IndexedGrammar.tiLiftRhsSym ] ;

/-! ### Lifting/projection for sentential forms -/

/-- Lift a sentential-form symbol from `g` to `termIsolate g`. -/
def tiLiftISym : g.ISym → (g.termIsolate).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (Sum.inl n) σ

/-- Project a sentential-form symbol from `termIsolate g` to `g`, sending
`Sum.inr t` to terminal `t`. -/
def tiProjISym : (g.termIsolate).ISym → g.ISym
  | .terminal t => .terminal t
  | .indexed (Sum.inl n) σ => .indexed n σ
  | .indexed (Sum.inr t) _ => .terminal t

theorem tiProjISym_tiLiftISym (s : g.ISym) : g.tiProjISym (g.tiLiftISym s) = s := by
  cases s <;> simp [tiLiftISym, tiProjISym]

theorem tiProjISym_terminal (t : T) :
    g.tiProjISym (.terminal t : (g.termIsolate).ISym) = .terminal t := by
  simp [tiProjISym]

/-! ### Forward direction: g.Generates w → termIsolate.Generates w -/

/-
In `termIsolate g`, `Sum.inr t` with empty stack derives terminal `t`.
-/
theorem termIsolate_inr_derives_terminal (t : T) (ht : t ∈ collectTerminals g) :
    (g.termIsolate).Derives [ISym.indexed (Sum.inr t) []] [ISym.terminal t] := by
  apply deri_of_tran;
  -- Apply the terminal rule to transform [ISym.indexed (Sum.inr t) []] into [ISym.terminal t].
  use ⟨Sum.inr t, none, [IRhsSymbol.terminal t]⟩, [], [], []
  simp [ht];
  exact ⟨ List.mem_append_right _ ( List.mem_map.mpr ⟨ t, ht, rfl ⟩ ), by rfl ⟩

/-
Every terminal in the RHS of a rule that's in g.rules is in collectTerminals.
-/
theorem terminal_in_collectTerminals {r : IRule T g.nt g.flag} (hr : r ∈ g.rules)
    {t : T} (ht : IRhsSymbol.terminal t ∈ r.rhs) :
    t ∈ collectTerminals g := by
  exact List.mem_flatten.mpr ⟨ _, List.mem_map.mpr ⟨ r, hr, rfl ⟩, List.mem_filterMap.mpr ⟨ _, ht, rfl ⟩ ⟩

/-
After applying a transformed rule, the `Sum.inr` nonterminals can be resolved to terminals.
-/
theorem termIsolate_resolve_inr (rhs : List (IRhsSymbol T g.nt g.flag))
    (σ : List g.flag) (r : IRule T g.nt g.flag) (hr : r ∈ g.rules) (hrhs : rhs = r.rhs) :
    (g.termIsolate).Derives
      (expandRhs g.termIsolate (rhs.map g.tiLiftRhsSym) σ)
      ((expandRhs g rhs σ).map g.tiLiftISym) := by
  have : ∀ s ∈ rhs, g.termIsolate.Derives (g.termIsolate.expandRhs (g.tiLiftRhsSym s :: []) σ) (List.map g.tiLiftISym (g.expandRhs [s] σ)) := by
    intro s hs;
    cases s <;> simp +decide [ *, IndexedGrammar.expandRhs, IndexedGrammar.tiLiftRhsSym, IndexedGrammar.tiLiftISym ];
    · rename_i t;
      exact deri_of_tran ⟨ ⟨ Sum.inr t, none, [ IRhsSymbol.terminal t ] ⟩, [ ], [ ], σ, by
        simp +decide [ IndexedGrammar.termIsolate ];
        grind +suggestions, by
        rfl, by
        rfl ⟩;
    · cases ‹Option g.flag› <;> tauto;
  have h_expand : ∀ {l : List (IRhsSymbol T g.nt g.flag)}, (∀ s ∈ l, g.termIsolate.Derives (g.termIsolate.expandRhs (g.tiLiftRhsSym s :: []) σ) (List.map g.tiLiftISym (g.expandRhs [s] σ))) → g.termIsolate.Derives (g.termIsolate.expandRhs (l.map g.tiLiftRhsSym) σ) (List.map g.tiLiftISym (g.expandRhs l σ)) := by
    intros l hl; induction' l with s l ih <;> simp_all +decide [ List.map ] ;
    · constructor;
    · convert deri_of_deri_deri _ _ using 1;
      exact map g.tiLiftISym ( g.expandRhs [ s ] σ ) ++ g.termIsolate.expandRhs ( map g.tiLiftRhsSym l ) σ;
      · convert deri_with_suffix _ hl.1 using 1;
      · convert deri_with_prefix _ ih using 1;
  exact h_expand this

/-
Lifting preserves one-step transforms.
-/
theorem termIsolate_lift_transforms {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) :
    (g.termIsolate).Derives (w₁.map g.tiLiftISym) (w₂.map g.tiLiftISym) := by
  obtain ⟨ n₁, n₂, t, ht, h' ⟩ := h;
  cases h';
  cases h : n₁.consume <;> simp_all +decide;
  · refine' deri_of_deri_deri _ _;
    exact map g.tiLiftISym n₂ ++ expandRhs g.termIsolate ( n₁.rhs.map g.tiLiftRhsSym ) ht ++ map g.tiLiftISym t;
    · refine' deri_of_tran _;
      use ⟨ Sum.inl n₁.lhs, none, n₁.rhs.map g.tiLiftRhsSym ⟩;
      unfold IndexedGrammar.termIsolate; aesop;
    · convert deri_with_prefix _ ( deri_with_suffix _ ( termIsolate_resolve_inr g n₁.rhs ht n₁ ‹_› rfl ) ) using 1;
      rw [ List.append_assoc ];
  · convert deri_of_tran_deri _ _ using 1;
    exact map g.tiLiftISym n₂ ++ expandRhs g.termIsolate ( n₁.rhs.map g.tiLiftRhsSym ) ht ++ map g.tiLiftISym t;
    · use ⟨ Sum.inl n₁.lhs, n₁.consume, n₁.rhs.map g.tiLiftRhsSym ⟩;
      unfold IndexedGrammar.termIsolate; aesop;
    · convert deri_with_suffix _ _ using 1;
      rotate_left;
      exact map g.tiLiftISym n₂ ++ map g.tiLiftISym ( g.expandRhs n₁.rhs ht );
      · convert deri_with_prefix _ _ using 1;
        exact?;
      · rw [ List.append_assoc ]

/-
Lifting preserves multi-step derivations.
-/
theorem termIsolate_lift_derives {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) :
    (g.termIsolate).Derives (w₁.map g.tiLiftISym) (w₂.map g.tiLiftISym) := by
  induction h;
  · constructor;
  · rename_i h₁ h₂ h₃;
    exact h₃.trans ( termIsolate_lift_transforms _ h₂ )

/-
Map terminal list commutes.
-/
theorem map_tiLiftISym_terminal (w : List T) :
    (w.map (ISym.terminal (g := g))).map g.tiLiftISym =
    w.map (ISym.terminal (g := g.termIsolate)) := by
  induction w <;> aesop

/-
Forward language inclusion.
-/
theorem termIsolate_language_forward {w : List T}
    (h : g.Generates w) : (g.termIsolate).Generates w := by
  refine' termIsolate_lift_derives _ h |> ( fun h' => h'.trans _ );
  unfold map tiLiftISym at *; aesop;

/-! ### Backward direction: termIsolate.Generates w → g.Generates w -/

/-- Project a sentential form. -/
def tiProjSF : List (g.termIsolate).ISym → List g.ISym :=
  List.map g.tiProjISym

/-- A sentential form is "resolved" if it contains no `Sum.inr` nonterminals. -/
def TIResolved (w : List (g.termIsolate).ISym) : Prop :=
  ∀ s ∈ w, ∀ t : T, ∀ σ, s ≠ ISym.indexed (Sum.inr t) σ

/-
Terminal sentential forms are resolved.
-/
theorem tiResolved_terminals (w : List T) :
    g.TIResolved (w.map (ISym.terminal (g := g.termIsolate))) := by
  intro s hs;
  induction w <;> aesop

/-
Projection commutes with expandRhs for transformed original rules.
-/
theorem tiProjSF_expandRhs_transformed (r : IRule T g.nt g.flag) (σ : List g.flag) :
    g.tiProjSF (expandRhs g.termIsolate (r.rhs.map g.tiLiftRhsSym) σ) =
    expandRhs g r.rhs σ := by
  unfold IndexedGrammar.tiProjSF IndexedGrammar.expandRhs;
  rw [ List.map_map ];
  rw [ List.map_map ];
  congr;
  ext s; cases s <;> simp +decide [ IndexedGrammar.tiLiftRhsSym, IndexedGrammar.tiProjISym ] ;
  cases ‹Option g.flag› <;> rfl

/-
Backward: one step in termIsolate that uses a transformed rule corresponds to a
    step in g (after projection).
-/
theorem termIsolate_proj_transforms {w₁ w₂ : List (g.termIsolate).ISym}
    (ht : (g.termIsolate).Transforms w₁ w₂) :
    g.Derives (g.tiProjSF w₁) (g.tiProjSF w₂) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := ht;
  by_cases hr' : r ∈ List.map (fun r => { lhs := Sum.inl r.lhs, consume := r.consume, rhs := List.map g.tiLiftRhsSym r.rhs }) g.rules;
  · obtain ⟨ r', hr', rfl ⟩ := List.mem_map.mp hr';
    cases h : r'.consume <;> simp_all +decide [ IndexedGrammar.tiProjSF ];
    · convert deri_of_tran _ using 1;
      use r', u.map g.tiProjISym, v.map g.tiProjISym, σ;
      simp +decide [ h, tiProjSF_expandRhs_transformed ];
      exact ⟨ by assumption, rfl, tiProjSF_expandRhs_transformed g r' σ ⟩;
    · convert deri_of_tran _ using 1;
      use r';
      use List.map g.tiProjISym u, List.map g.tiProjISym v, σ;
      simp +decide [ h, tiProjSF_expandRhs_transformed ];
      exact ⟨ by assumption, rfl, tiProjSF_expandRhs_transformed g r' σ ⟩;
  · unfold termIsolate at hr; simp_all +decide ;
    rcases hr with ⟨ a, ha, rfl ⟩ ; simp_all +decide [ IndexedGrammar.expandRhs ] ;
    simp +decide [ IndexedGrammar.tiProjSF ];
    convert deri_self _ _ using 1

/-
Backward: multi-step derivation projection.
-/
theorem termIsolate_proj_derives {w₁ w₂ : List (g.termIsolate).ISym}
    (hd : (g.termIsolate).Derives w₁ w₂) :
    g.Derives (g.tiProjSF w₁) (g.tiProjSF w₂) := by
  induction hd;
  · exact?;
  · rename_i h₁ h₂ h₃;
    apply deri_of_deri_deri h₃;
    exact?

/-
Projection of terminal list is terminal list.
-/
theorem tiProjSF_terminal (w : List T) :
    g.tiProjSF (w.map (ISym.terminal (g := g.termIsolate))) =
    w.map (ISym.terminal (g := g)) := by
  unfold IndexedGrammar.tiProjSF;
  unfold IndexedGrammar.tiProjISym; aesop;

/-
Backward language inclusion.
-/
theorem termIsolate_language_backward {w : List T}
    (h : (g.termIsolate).Generates w) : g.Generates w := by
  -- Apply the termIsolate_proj_derives theorem to go from the termIsolate derivation to the original grammar's derivation.
  have h_proj : g.Derives (g.tiProjSF [ISym.indexed (Sum.inl g.initial) []]) (g.tiProjSF (w.map (ISym.terminal (g := g.termIsolate)))) := by
    -- Apply the termIsolate_proj_derives theorem to go from the termIsolate derivation to the original grammar's derivation, using the fact that the terminal-isolated grammar's derivation is equivalent to the original grammar's derivation.
    apply termIsolate_proj_derives; assumption;
  convert h_proj using 1;
  unfold IndexedGrammar.tiProjSF; simp +decide [ IndexedGrammar.Generates ] ;
  congr! 2

/-! ### Main result -/

theorem exists_terminalsIsolated' (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧ g'.TerminalsIsolated ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  exact ⟨g.termIsolate, g.termIsolate_noEpsilon hne, g.termIsolate_terminalsIsolated,
    fun w _ => ⟨g.termIsolate_language_backward, g.termIsolate_language_forward⟩⟩

end TerminalIsolation

end IndexedGrammar