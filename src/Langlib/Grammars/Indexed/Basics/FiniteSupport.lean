module

public import Langlib.Grammars.Indexed.Definition
public import Mathlib.Data.Finset.Basic
@[expose]
public section

/-! # Finite nonterminal and flag support for indexed grammars

Indexed grammars store their rules in a finite list. Even if the ambient nonterminal and
flag types are infinite, every derivation from the initial symbol only uses nonterminals and
flags mentioned by the initial symbol or by the rules. This file restricts an indexed grammar
to those finite supports while preserving its language.
-/

noncomputable section

open scoped Classical

variable {T : Type}

namespace IndexedGrammar

/-! ## Syntactic supports -/

/-- Nonterminals mentioned by a right-hand-side symbol. -/
def rhsSymbolNTs {N F : Type} : IRhsSymbol T N F → List N
  | IRhsSymbol.terminal _ => []
  | IRhsSymbol.nonterminal n _ => [n]

/-- Nonterminals mentioned by a rule, including its left-hand side. -/
def ruleNTs {N F : Type} (r : IRule T N F) : List N :=
  r.lhs :: r.rhs.flatMap rhsSymbolNTs

/-- Flags mentioned by a right-hand-side symbol as pushed flags. -/
def rhsSymbolFlags {N F : Type} : IRhsSymbol T N F → List F
  | IRhsSymbol.terminal _ => []
  | IRhsSymbol.nonterminal _ none => []
  | IRhsSymbol.nonterminal _ (some f) => [f]

/-- Flags mentioned by a rule, including consumed and pushed flags. -/
def ruleFlags {N F : Type} (r : IRule T N F) : List F :=
  r.consume.toList ++ r.rhs.flatMap rhsSymbolFlags

/-- The finite set of nonterminals used by an indexed grammar. -/
def usedNTs (g : IndexedGrammar T) : Finset g.nt :=
  (g.initial :: g.rules.flatMap ruleNTs).toFinset

/-- The finite set of flags used by an indexed grammar. -/
def usedFlags (g : IndexedGrammar T) : Finset g.flag :=
  (g.rules.flatMap ruleFlags).toFinset

lemma initial_mem_usedNTs (g : IndexedGrammar T) : g.initial ∈ usedNTs g := by
  unfold usedNTs
  simp

private lemma terminal_not_mem_rhsSymbolNTs {N F : Type} {n : N} {t : T} :
    n ∉ rhsSymbolNTs (F := F) (IRhsSymbol.terminal t) := by
  simp [rhsSymbolNTs]

lemma rhs_nonterminal_mem_ruleNTs {N F : Type} {r : IRule T N F}
    {n : N} {push : Option F} (h : IRhsSymbol.nonterminal n push ∈ r.rhs) :
    n ∈ ruleNTs r := by
  unfold ruleNTs
  exact List.mem_cons_of_mem _ <|
    List.mem_flatMap.mpr ⟨IRhsSymbol.nonterminal n push, h, by simp [rhsSymbolNTs]⟩

lemma lhs_mem_ruleNTs {N F : Type} (r : IRule T N F) : r.lhs ∈ ruleNTs r := by
  simp [ruleNTs]

lemma ruleNT_mem_usedNTs {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {n : g.nt} (hn : n ∈ ruleNTs r) :
    n ∈ usedNTs g := by
  unfold usedNTs
  rw [List.mem_toFinset]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, hr, hn⟩)

lemma rule_lhs_mem_usedNTs {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) : r.lhs ∈ usedNTs g :=
  ruleNT_mem_usedNTs hr (lhs_mem_ruleNTs r)

lemma rule_rhs_nt_mem_usedNTs {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {n : g.nt} {push : Option g.flag}
    (h : IRhsSymbol.nonterminal n push ∈ r.rhs) :
    n ∈ usedNTs g :=
  ruleNT_mem_usedNTs hr (rhs_nonterminal_mem_ruleNTs h)

lemma consume_mem_ruleFlags {N F : Type} {r : IRule T N F} {f : F}
    (h : r.consume = some f) : f ∈ ruleFlags r := by
  unfold ruleFlags
  simp [h]

lemma rhs_push_mem_ruleFlags {N F : Type} {r : IRule T N F}
    {n : N} {f : F} (h : IRhsSymbol.nonterminal n (some f) ∈ r.rhs) :
    f ∈ ruleFlags r := by
  unfold ruleFlags
  exact List.mem_append.mpr <|
    Or.inr (List.mem_flatMap.mpr
      ⟨IRhsSymbol.nonterminal n (some f), h, by simp [rhsSymbolFlags]⟩)

lemma ruleFlag_mem_usedFlags {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {f : g.flag} (hf : f ∈ ruleFlags r) :
    f ∈ usedFlags g := by
  unfold usedFlags
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr ⟨r, hr, hf⟩

lemma rule_consume_mem_usedFlags {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {f : g.flag} (h : r.consume = some f) :
    f ∈ usedFlags g :=
  ruleFlag_mem_usedFlags hr (consume_mem_ruleFlags h)

lemma rule_consume_mem_usedFlags_of_mem {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {f : g.flag} (h : f ∈ r.consume) :
    f ∈ usedFlags g :=
  rule_consume_mem_usedFlags hr (by simpa using h)

lemma rule_rhs_push_mem_usedFlags {g : IndexedGrammar T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) {n : g.nt} {f : g.flag}
    (h : IRhsSymbol.nonterminal n (some f) ∈ r.rhs) :
    f ∈ usedFlags g :=
  ruleFlag_mem_usedFlags hr (rhs_push_mem_ruleFlags h)

/-! ## Restricted grammar -/

/-- The subtype of nonterminals used by `g`. -/
abbrev UsedNT (g : IndexedGrammar T) := {n : g.nt // n ∈ usedNTs g}

/-- The subtype of flags used by `g`. -/
abbrev UsedFlag (g : IndexedGrammar T) := {f : g.flag // f ∈ usedFlags g}

instance usedNT_fintype (g : IndexedGrammar T) : Fintype (UsedNT g) :=
  Fintype.subtype (usedNTs g) (fun _ => Iff.rfl)

instance usedFlag_fintype (g : IndexedGrammar T) : Fintype (UsedFlag g) :=
  Fintype.subtype (usedFlags g) (fun _ => Iff.rfl)

def restrictConsume (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) : Option (UsedFlag g) :=
  r.consume.attach.map fun f => ⟨f.1, rule_consume_mem_usedFlags_of_mem hr f.2⟩

def restrictPush (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) {n : g.nt} (push : Option g.flag)
    (hs : IRhsSymbol.nonterminal n push ∈ r.rhs) : Option (UsedFlag g) :=
  match push with
  | none => none
  | some f => some ⟨f, rule_rhs_push_mem_usedFlags hr hs⟩

def restrictRhsSymbol (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) (s : IRhsSymbol T g.nt g.flag) (hs : s ∈ r.rhs) :
    IRhsSymbol T (UsedNT g) (UsedFlag g) :=
  match s with
  | IRhsSymbol.terminal t => IRhsSymbol.terminal t
  | IRhsSymbol.nonterminal n push =>
      IRhsSymbol.nonterminal
        ⟨n, rule_rhs_nt_mem_usedNTs hr hs⟩
        (restrictPush g r hr push hs)

def restrictRhs (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) : List (IRhsSymbol T (UsedNT g) (UsedFlag g)) :=
  r.rhs.attach.map fun s => restrictRhsSymbol g r hr s.1 s.2

def restrictRule (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) : IRule T (UsedNT g) (UsedFlag g) where
  lhs := ⟨r.lhs, rule_lhs_mem_usedNTs hr⟩
  consume := restrictConsume g r hr
  rhs := restrictRhs g r hr

/-- The indexed grammar restricted to the finite nonterminal and flag supports used by `g`. -/
def toFiniteSupport (g : IndexedGrammar T) : IndexedGrammar T where
  nt := UsedNT g
  flag := UsedFlag g
  initial := ⟨g.initial, initial_mem_usedNTs g⟩
  rules := g.rules.attach.map fun r => restrictRule g r.1 r.2

instance toFiniteSupport_nt_fintype (g : IndexedGrammar T) :
    Fintype g.toFiniteSupport.nt :=
  usedNT_fintype g

instance toFiniteSupport_flag_fintype (g : IndexedGrammar T) :
    Fintype g.toFiniteSupport.flag :=
  usedFlag_fintype g

/-! ## Embedding restricted syntax back into `g` -/

def embedFlag (g : IndexedGrammar T) : UsedFlag g → g.flag :=
  Subtype.val

def embedRhsSymbol (g : IndexedGrammar T) :
    IRhsSymbol T (UsedNT g) (UsedFlag g) → IRhsSymbol T g.nt g.flag
  | IRhsSymbol.terminal t => IRhsSymbol.terminal t
  | IRhsSymbol.nonterminal n push => IRhsSymbol.nonterminal n.1 (push.map Subtype.val)

def embedISym (g : IndexedGrammar T) : g.toFiniteSupport.ISym → g.ISym
  | ISym.terminal t => ISym.terminal t
  | ISym.indexed n σ => ISym.indexed n.1 (σ.map Subtype.val)

private lemma option_pmap_val_eq {α : Type} {S : Finset α} (o : Option α)
    (p : ∀ a, a ∈ o → a ∈ S) :
    (o.pmap (fun a ha => (⟨a, p a ha⟩ : {a : α // a ∈ S})) (fun _ h => h)).map Subtype.val = o := by
  cases o <;> rfl

lemma restrictConsume_val (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) :
    (restrictConsume g r hr).map Subtype.val = r.consume := by
  unfold restrictConsume
  rcases r with ⟨lhs, consume, rhs⟩
  cases consume <;> rfl

lemma restrictPush_val (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) {n : g.nt} (push : Option g.flag)
    (hs : IRhsSymbol.nonterminal n push ∈ r.rhs) :
    (restrictPush g r hr push hs).map Subtype.val = push := by
  unfold restrictPush
  cases push <;> rfl

lemma embed_restrictRhsSymbol (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) (s : IRhsSymbol T g.nt g.flag) (hs : s ∈ r.rhs) :
    embedRhsSymbol g (restrictRhsSymbol g r hr s hs) = s := by
  cases s with
  | terminal t => rfl
  | nonterminal n push =>
      simp [restrictRhsSymbol, embedRhsSymbol]
      exact restrictPush_val g r hr push hs

lemma embed_restrictRhs (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) :
    (restrictRhs g r hr).map (embedRhsSymbol g) = r.rhs := by
  unfold restrictRhs
  rw [List.map_map]
  simp [Function.comp_def, embed_restrictRhsSymbol]

lemma embedRhsSymbol_injective (g : IndexedGrammar T) :
    Function.Injective (embedRhsSymbol g) := by
  intro a b h
  cases a <;> cases b <;> simp [embedRhsSymbol] at h ⊢
  · exact h
  · obtain ⟨hn, hpush⟩ := h
    constructor
    · exact hn
    · cases ‹Option (UsedFlag g)› <;> cases ‹Option (UsedFlag g)› <;>
        simp at hpush ⊢
      exact hpush

lemma expandRhs_embed (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T (UsedNT g) (UsedFlag g))) (σ : List (UsedFlag g)) :
    (g.toFiniteSupport.expandRhs rhs σ).map (embedISym g) =
      g.expandRhs (rhs.map (embedRhsSymbol g)) (σ.map Subtype.val) := by
  unfold expandRhs
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro s _hs
  cases s with
  | terminal t => rfl
  | nonterminal n push =>
      cases push <;> rfl

lemma expandRhs_restrict (g : IndexedGrammar T) (r : IRule T g.nt g.flag)
    (hr : r ∈ g.rules) (σ : List (UsedFlag g)) :
    (g.toFiniteSupport.expandRhs (restrictRule g r hr).rhs σ).map (embedISym g) =
      g.expandRhs r.rhs (σ.map Subtype.val) := by
  rw [expandRhs_embed]
  simp [restrictRule, embed_restrictRhs]

lemma restrictRule_mem_toFiniteSupport (g : IndexedGrammar T)
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules) :
    restrictRule g r hr ∈ g.toFiniteSupport.rules := by
  unfold toFiniteSupport
  exact List.mem_map.mpr ⟨⟨r, hr⟩, by simp, rfl⟩

lemma mem_toFiniteSupport_rules (g : IndexedGrammar T)
    {r' : IRule T g.toFiniteSupport.nt g.toFiniteSupport.flag}
    (hr' : r' ∈ g.toFiniteSupport.rules) :
    ∃ (r : IRule T g.nt g.flag) (hr : r ∈ g.rules), r' = restrictRule g r hr := by
  unfold toFiniteSupport at hr'
  obtain ⟨r, _hr, rfl⟩ := List.mem_map.mp hr'
  exact ⟨r.1, r.2, rfl⟩

/-! ## Finite-support sentential forms -/

def stackSupported (g : IndexedGrammar T) (σ : List g.flag) : Prop :=
  ∀ f ∈ σ, f ∈ usedFlags g

def symSupported (g : IndexedGrammar T) : g.ISym → Prop
  | ISym.terminal _ => True
  | ISym.indexed n σ => n ∈ usedNTs g ∧ stackSupported g σ

def sententialSupported (g : IndexedGrammar T) (w : List g.ISym) : Prop :=
  ∀ s ∈ w, symSupported g s

lemma stackSupported_tail {g : IndexedGrammar T} {f : g.flag} {σ : List g.flag}
    (h : stackSupported g (f :: σ)) : stackSupported g σ := by
  intro a ha
  exact h a (List.mem_cons_of_mem _ ha)

lemma stackSupported_cons {g : IndexedGrammar T} {f : g.flag} {σ : List g.flag}
    (hf : f ∈ usedFlags g) (hσ : stackSupported g σ) :
    stackSupported g (f :: σ) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hf
  · exact hσ a ha

lemma sententialSupported_initial (g : IndexedGrammar T) :
    sententialSupported g [ISym.indexed g.initial []] := by
  intro s hs
  simp at hs
  subst s
  exact ⟨initial_mem_usedNTs g, by intro f hf; simp at hf⟩

private lemma support_of_source_occurrence_none {g : IndexedGrammar T}
    {w u v : List g.ISym} {lhs : g.nt} {σ : List g.flag}
    (hsupp : sententialSupported g w)
    (hw : w = u ++ [ISym.indexed lhs σ] ++ v) :
    stackSupported g σ := by
  have hmem : ISym.indexed lhs σ ∈ w := by
    rw [hw]
    simp
  exact (hsupp _ hmem).2

private lemma support_of_source_occurrence_some {g : IndexedGrammar T}
    {w u v : List g.ISym} {lhs : g.nt} {f : g.flag} {σ : List g.flag}
    (hsupp : sententialSupported g w)
    (hw : w = u ++ [ISym.indexed lhs (f :: σ)] ++ v) :
    stackSupported g σ := by
  have hmem : ISym.indexed lhs (f :: σ) ∈ w := by
    rw [hw]
    simp
  exact stackSupported_tail (hsupp _ hmem).2

lemma expandRhs_supported {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules) {σ : List g.flag}
    (hσ : stackSupported g σ) :
    sententialSupported g (g.expandRhs r.rhs σ) := by
  intro s hs
  unfold expandRhs at hs
  rw [List.mem_map] at hs
  obtain ⟨a, ha, hsa⟩ := hs
  cases a with
  | terminal t =>
      subst s
      trivial
  | nonterminal n push =>
      cases push with
      | none =>
          subst s
          exact ⟨rule_rhs_nt_mem_usedNTs hr ha, hσ⟩
      | some f =>
          subst s
          exact ⟨rule_rhs_nt_mem_usedNTs hr ha,
            stackSupported_cons (rule_rhs_push_mem_usedFlags hr ha) hσ⟩

lemma transforms_supported {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) (hsupp : sententialSupported g w₁) :
    sententialSupported g w₂ := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  subst w₂
  have hσ : stackSupported g σ := by
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact support_of_source_occurrence_none hsupp hw₁
    | some f =>
        rw [hc] at hw₁
        exact support_of_source_occurrence_some hsupp hw₁
  intro s hs
  rcases List.mem_append.mp hs with hleft | hv
  · rcases List.mem_append.mp hleft with hu | hmid
    · cases hc : r.consume with
      | none =>
          rw [hc] at hw₁
          exact hsupp s (by rw [hw₁]; simp [hu])
      | some f =>
          rw [hc] at hw₁
          exact hsupp s (by rw [hw₁]; simp [hu])
    · exact expandRhs_supported hr hσ s hmid
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hv])
    | some f =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hv])

lemma derives_supported {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) (hsupp : sententialSupported g w₁) :
    sententialSupported g w₂ := by
  induction h with
  | refl => exact hsupp
  | tail _ hstep ih => exact transforms_supported hstep ih

/-! ## Restricting supported sentential forms -/

def restrictStack (g : IndexedGrammar T) (σ : List g.flag)
    (hσ : stackSupported g σ) : List (UsedFlag g) :=
  σ.attach.map fun f => ⟨f.1, hσ f.1 f.2⟩

def restrictISym (g : IndexedGrammar T) (s : g.ISym)
    (hs : symSupported g s) : g.toFiniteSupport.ISym :=
  match s with
  | ISym.terminal t => ISym.terminal t
  | ISym.indexed n σ =>
      ISym.indexed ⟨n, hs.1⟩ (restrictStack g σ hs.2)

def restrictSF (g : IndexedGrammar T) (w : List g.ISym)
    (hw : sententialSupported g w) : List g.toFiniteSupport.ISym :=
  w.attach.map fun s => restrictISym g s.1 (hw s.1 s.2)

lemma map_val_restrictStack (g : IndexedGrammar T) (σ : List g.flag)
    (hσ : stackSupported g σ) :
    (restrictStack g σ hσ).map Subtype.val = σ := by
  unfold restrictStack
  simp

lemma unattach_restrictStack (g : IndexedGrammar T) (σ : List g.flag)
    (hσ : stackSupported g σ) :
    (restrictStack g σ hσ).unattach = σ :=
  map_val_restrictStack g σ hσ

lemma embed_restrictISym (g : IndexedGrammar T) (s : g.ISym)
    (hs : symSupported g s) :
    embedISym g (restrictISym g s hs) = s := by
  cases s with
  | terminal t => rfl
  | indexed n σ =>
      simp [restrictISym, embedISym]
      exact unattach_restrictStack g σ hs.2

lemma embed_restrictSF (g : IndexedGrammar T) (w : List g.ISym)
    (hw : sententialSupported g w) :
    (restrictSF g w hw).map (embedISym g) = w := by
  unfold restrictSF
  rw [List.map_map]
  simp [Function.comp_def, embed_restrictISym]

lemma embedISym_injective (g : IndexedGrammar T) : Function.Injective (embedISym g) := by
  intro a b h
  cases a <;> cases b <;> simp [embedISym] at h ⊢
  · exact h
  · obtain ⟨hn, hσ⟩ := h
    constructor
    · exact hn
    · exact List.map_injective_iff.mpr Subtype.val_injective hσ

lemma restrictSF_terminal (g : IndexedGrammar T) (w : List T)
    (hw : sententialSupported g (w.map ISym.terminal)) :
    restrictSF g (w.map ISym.terminal) hw = w.map ISym.terminal := by
  apply List.map_injective_iff.mpr (embedISym_injective g)
  simp [embed_restrictSF, embedISym]

lemma restrictSF_initial (g : IndexedGrammar T) :
    restrictSF g [ISym.indexed g.initial []] (sententialSupported_initial g) =
      [(ISym.indexed ⟨g.initial, initial_mem_usedNTs g⟩ [] : g.toFiniteSupport.ISym)] := by
  apply List.map_injective_iff.mpr (embedISym_injective g)
  simp [embed_restrictSF, embedISym]

/-! ## Derivation correspondence -/

theorem transforms_embed {g : IndexedGrammar T}
    {w₁ w₂ : List g.toFiniteSupport.ISym}
    (h : g.toFiniteSupport.Transforms w₁ w₂) :
    g.Transforms (w₁.map (embedISym g)) (w₂.map (embedISym g)) := by
  obtain ⟨r', u, v, σ, hr', hw₁, hw₂⟩ := h
  obtain ⟨r, hr, rfl⟩ := mem_toFiniteSupport_rules g hr'
  refine ⟨r, u.map (embedISym g), v.map (embedISym g), σ.map Subtype.val, hr, ?_, ?_⟩
  · cases hc' : restrictConsume g r hr with
    | none =>
      have hc : r.consume = none := by
        have hmap := congrArg (Option.map Subtype.val) hc'
        rw [restrictConsume_val] at hmap
        simpa using hmap
      simp [restrictRule, hc'] at hw₁
      have hw₁' := congrArg (List.map (embedISym g)) hw₁
      simpa [List.map_append, embedISym, hc] using hw₁'
    | some f =>
      have hc : r.consume = some f.1 := by
        have hmap := congrArg (Option.map Subtype.val) hc'
        rw [restrictConsume_val] at hmap
        simpa using hmap
      simp [restrictRule, hc'] at hw₁
      have hw₁' := congrArg (List.map (embedISym g)) hw₁
      simpa [List.map_append, embedISym, hc] using hw₁'
  · have hw₂' := congrArg (List.map (embedISym g)) hw₂
    simpa [List.map_append, List.append_assoc, expandRhs_restrict] using hw₂'

theorem derives_embed {g : IndexedGrammar T}
    {w₁ w₂ : List g.toFiniteSupport.ISym}
    (h : g.toFiniteSupport.Derives w₁ w₂) :
    g.Derives (w₁.map (embedISym g)) (w₂.map (embedISym g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (transforms_embed hstep)

theorem transforms_restrict {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) (hsupp : sententialSupported g w₁) :
    g.toFiniteSupport.Transforms
      (restrictSF g w₁ hsupp)
      (restrictSF g w₂ (transforms_supported h hsupp)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  subst w₂
  have hσ : stackSupported g σ := by
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact support_of_source_occurrence_none hsupp hw₁
    | some f =>
        rw [hc] at hw₁
        exact support_of_source_occurrence_some hsupp hw₁
  let hu : sententialSupported g u := by
    intro s hs
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hs])
    | some f =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hs])
  let hv : sententialSupported g v := by
    intro s hs
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hs])
    | some f =>
        rw [hc] at hw₁
        exact hsupp s (by rw [hw₁]; simp [hs])
  refine ⟨restrictRule g r hr, restrictSF g u hu, restrictSF g v hv,
    restrictStack g σ hσ, restrictRule_mem_toFiniteSupport g hr, ?_, ?_⟩
  · cases hc' : restrictConsume g r hr with
    | none =>
        have hc : r.consume = none := by
          have hmap := congrArg (Option.map Subtype.val) hc'
          rw [restrictConsume_val] at hmap
          simpa using hmap
        simp [restrictRule, hc']
        apply List.map_injective_iff.mpr (embedISym_injective g)
        rw [hc] at hw₁
        simp [List.map_append, embed_restrictSF, embedISym, unattach_restrictStack, hw₁]
    | some f =>
        have hc : r.consume = some f.1 := by
          have hmap := congrArg (Option.map Subtype.val) hc'
          rw [restrictConsume_val] at hmap
          simpa using hmap
        simp [restrictRule, hc']
        apply List.map_injective_iff.mpr (embedISym_injective g)
        rw [hc] at hw₁
        simp [List.map_append, embed_restrictSF, embedISym, unattach_restrictStack, hw₁]
  · apply List.map_injective_iff.mpr (embedISym_injective g)
    simp [List.map_append, List.append_assoc, embed_restrictSF,
      expandRhs_restrict, unattach_restrictStack]

theorem derives_restrict {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) (hsupp : sententialSupported g w₁) :
    g.toFiniteSupport.Derives
      (restrictSF g w₁ hsupp)
      (restrictSF g w₂ (derives_supported h hsupp)) := by
  induction h with
  | refl =>
      convert (Relation.ReflTransGen.refl :
        g.toFiniteSupport.Derives (restrictSF g w₁ hsupp) (restrictSF g w₁ hsupp)) using 1
  | tail hprev hstep ih =>
      let hmid := derives_supported hprev hsupp
      have hstep' := transforms_restrict hstep hmid
      convert ih.tail hstep' using 1

/-! ## Language equality -/

theorem toFiniteSupport_language (g : IndexedGrammar T) :
    g.toFiniteSupport.Language = g.Language := by
  ext w
  constructor
  · intro hw
    change g.toFiniteSupport.Derives
      [ISym.indexed ⟨g.initial, initial_mem_usedNTs g⟩ []] (w.map ISym.terminal) at hw
    have hder := derives_embed hw
    simpa [Language, Generates, toFiniteSupport, embedISym] using hder
  · intro hw
    change g.Derives [ISym.indexed g.initial []] (w.map ISym.terminal) at hw
    have hder := derives_restrict hw (sententialSupported_initial g)
    change g.toFiniteSupport.Derives
      [ISym.indexed ⟨g.initial, initial_mem_usedNTs g⟩ []] (w.map ISym.terminal)
    convert hder using 1
    exact (restrictSF_terminal g w _).symm

/-- Every indexed grammar has an equivalent grammar whose nonterminal and flag types are finite. -/
theorem exists_finiteSupport (g : IndexedGrammar T) :
    ∃ g' : IndexedGrammar T, ∃ _ : Fintype g'.nt, ∃ _ : Fintype g'.flag,
      g'.Language = g.Language :=
  ⟨g.toFiniteSupport, inferInstance, inferInstance, toFiniteSupport_language g⟩

/-! ## Preservation of normal form -/

private lemma usedNT_ne_initial {g : IndexedGrammar T} {n : g.nt}
    {hn : n ∈ usedNTs g} (h : n ≠ g.initial) :
    (⟨n, hn⟩ : UsedNT g) ≠ ⟨g.initial, initial_mem_usedNTs g⟩ := by
  intro heq
  exact h (congrArg Subtype.val heq)

theorem restrictRule_isNF {g : IndexedGrammar T} [DecidableEq g.nt]
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules)
    (hNF : IRule.IsNF r g.initial) :
    IRule.IsNF (restrictRule g r hr) (⟨g.initial, initial_mem_usedNTs g⟩ : UsedNT g) := by
  rcases hNF with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
    left
    refine ⟨?_, ⟨⟨B, ?_⟩, ⟨C, ?_⟩, ?_, ?_, ?_⟩⟩
    · simp [restrictRule, restrictConsume, hc]
    · exact rule_rhs_nt_mem_usedNTs (push := none) hr (by
        rw [hrhs]
        simp)
    · exact rule_rhs_nt_mem_usedNTs (push := none) hr (by
        rw [hrhs]
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · apply List.map_injective_iff.mpr (embedRhsSymbol_injective g)
      simp [restrictRule, embed_restrictRhs, embedRhsSymbol, hrhs]
    · exact usedNT_ne_initial hB
    · exact usedNT_ne_initial hC
  · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
    right
    left
    refine ⟨⟨f, rule_consume_mem_usedFlags hr hc⟩, ?_, ⟨⟨B, ?_⟩, ?_, ?_⟩⟩
    · simp [restrictRule, restrictConsume, hc]
    · exact rule_rhs_nt_mem_usedNTs (push := none) hr (by
        rw [hrhs]
        exact List.mem_singleton_self _)
    · apply List.map_injective_iff.mpr (embedRhsSymbol_injective g)
      simp [restrictRule, embed_restrictRhs, embedRhsSymbol, hrhs]
    · exact usedNT_ne_initial hB
  · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
    right
    right
    left
    refine ⟨?_, ⟨⟨B, ?_⟩, ⟨f, ?_⟩, ?_, ?_⟩⟩
    · simp [restrictRule, restrictConsume, hc]
    · exact rule_rhs_nt_mem_usedNTs (push := some f) hr (by
        rw [hrhs]
        exact List.mem_singleton_self _)
    · exact rule_rhs_push_mem_usedFlags (n := B) (f := f) hr (by
        rw [hrhs]
        exact List.mem_singleton_self _)
    · apply List.map_injective_iff.mpr (embedRhsSymbol_injective g)
      simp [restrictRule, embed_restrictRhs, embedRhsSymbol, hrhs]
    · exact usedNT_ne_initial hB
  · rcases hterm with ⟨hc, a, hrhs⟩
    right
    right
    right
    refine ⟨?_, a, ?_⟩
    · simp [restrictRule, restrictConsume, hc]
    · apply List.map_injective_iff.mpr (embedRhsSymbol_injective g)
      simp [restrictRule, embed_restrictRhs, embedRhsSymbol, hrhs]

theorem toFiniteSupport_isNormalForm {g : IndexedGrammar T} [DecidableEq g.nt]
    (hNF : g.IsNormalForm) : g.toFiniteSupport.IsNormalForm := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := mem_toFiniteSupport_rules g hr
  exact restrictRule_isNF hr₀ (hNF r₀ hr₀)

end IndexedGrammar

end
