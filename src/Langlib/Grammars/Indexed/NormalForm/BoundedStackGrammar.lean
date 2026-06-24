module

public import Langlib.Grammars.Indexed.NormalForm.Bounds
public import Langlib.Grammars.Indexed.NormalForm.ParseTree
public import Langlib.Grammars.Indexed.NormalForm.Shrinking
public import Langlib.Classes.ContextSensitive.Definition
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
@[expose]
public section

/-!
# Bounded-stack compilation for indexed normal form

For a fixed stack bound `B`, an indexed grammar has only finitely many visible stacked
nonterminals `(A, σ)` with `|σ| ≤ B`. This file compiles the `B`-bounded slice of an indexed
grammar into an unrestricted grammar over those finite stacked nonterminals.

The construction is concrete infrastructure for the finite normal-form simulator: once a
derivation is known to stay inside a fixed stack bound, its one-step indexed rewrites are
ordinary noncontracting grammar rewrites over the finite alphabet of bounded stacks.
-/

variable {T : Type}

namespace IndexedGrammar

/-- Nonterminals of the fixed-stack-bound compilation: an indexed nonterminal together with a
stack whose height is at most `B`. -/
abbrev BoundedStackNT (g : IndexedGrammar T) (B : ℕ) : Type :=
  g.nt × {σ : List g.flag // σ.length ≤ B}

noncomputable instance boundedStackStackFintype {g : IndexedGrammar T}
    [Fintype g.flag] (B : ℕ) :
    Fintype {σ : List g.flag // σ.length ≤ B} :=
  (List.finite_length_le g.flag B).fintype

noncomputable instance boundedStackNTFintype {g : IndexedGrammar T}
    [Fintype g.nt] [Fintype g.flag] (B : ℕ) :
    Fintype (BoundedStackNT g B) := by
  letI : Fintype {σ : List g.flag // σ.length ≤ B} :=
    boundedStackStackFintype (g := g) B
  exact instFintypeProd g.nt {σ : List g.flag // σ.length ≤ B}

/-- All stacks of height at most `B`, as a finite list. -/
noncomputable def boundedStacksList (g : IndexedGrammar T) [Fintype g.flag]
    (B : ℕ) : List {σ : List g.flag // σ.length ≤ B} :=
  (Finset.univ : Finset {σ : List g.flag // σ.length ≤ B}).toList

@[simp] theorem mem_boundedStacksList {g : IndexedGrammar T} [Fintype g.flag]
    {B : ℕ} (σ : {σ : List g.flag // σ.length ≤ B}) :
    σ ∈ boundedStacksList g B := by
  classical
  simp [boundedStacksList]

/-- Translate one bounded indexed symbol into an unrestricted-grammar symbol. Symbols whose
stack exceeds the bound are rejected. -/
def boundedSymbol? {g : IndexedGrammar T} (B : ℕ) :
    g.ISym → Option (symbol T (BoundedStackNT g B))
  | ISym.terminal a => some (symbol.terminal a)
  | ISym.indexed A σ =>
      if h : σ.length ≤ B then
        some (symbol.nonterminal (A, ⟨σ, h⟩))
      else
        none

/-- Translate a sentential form if every attached stack is within the bound. -/
def boundedSentential? {g : IndexedGrammar T} (B : ℕ) :
    List g.ISym → Option (List (symbol T (BoundedStackNT g B)))
  | [] => some []
  | s :: w =>
      match boundedSymbol? B s, boundedSentential? B w with
      | some s', some w' => some (s' :: w')
      | _, _ => none

/-- Forget the fixed stack bound annotation and return to indexed sentential symbols. -/
def eraseBoundedSymbol {g : IndexedGrammar T} {B : ℕ} :
    symbol T (BoundedStackNT g B) → g.ISym
  | symbol.terminal a => ISym.terminal a
  | symbol.nonterminal Aσ => ISym.indexed Aσ.1 Aσ.2.1

def eraseBoundedSentential {g : IndexedGrammar T} {B : ℕ}
    (w : List (symbol T (BoundedStackNT g B))) : List g.ISym :=
  w.map eraseBoundedSymbol

@[simp] theorem eraseBoundedSymbol_terminal {g : IndexedGrammar T} {B : ℕ}
    (a : T) :
    eraseBoundedSymbol (g := g) (B := B) (symbol.terminal a) = ISym.terminal a := rfl

@[simp] theorem eraseBoundedSymbol_nonterminal {g : IndexedGrammar T} {B : ℕ}
    (A : g.nt) (σ : {σ : List g.flag // σ.length ≤ B}) :
    eraseBoundedSymbol (g := g) (B := B) (symbol.nonterminal (A, σ)) =
      ISym.indexed A σ.1 := rfl

@[simp] theorem eraseBoundedSentential_nil {g : IndexedGrammar T} {B : ℕ} :
    eraseBoundedSentential ([] : List (symbol T (BoundedStackNT g B))) = [] := rfl

@[simp] theorem eraseBoundedSentential_cons {g : IndexedGrammar T} {B : ℕ}
    (s : symbol T (BoundedStackNT g B))
    (w : List (symbol T (BoundedStackNT g B))) :
    eraseBoundedSentential (s :: w) =
      eraseBoundedSymbol s :: eraseBoundedSentential w := rfl

@[simp] theorem eraseBoundedSentential_append {g : IndexedGrammar T} {B : ℕ}
    (u v : List (symbol T (BoundedStackNT g B))) :
    eraseBoundedSentential (u ++ v) =
      eraseBoundedSentential u ++ eraseBoundedSentential v := by
  simp [eraseBoundedSentential, List.map_append]

@[simp] theorem eraseBoundedSentential_map_terminal {g : IndexedGrammar T} {B : ℕ}
    (w : List T) :
    eraseBoundedSentential
        (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) =
      w.map fun a => (ISym.terminal a : g.ISym) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

theorem sententialMaxStackHeight_eraseBoundedSentential_le {g : IndexedGrammar T}
    {B : ℕ} (w : List (symbol T (BoundedStackNT g B))) :
    sententialMaxStackHeight (eraseBoundedSentential w) ≤ B := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          simpa [eraseBoundedSentential] using ih
      | nonterminal Aσ =>
          exact max_le (by simpa using Aσ.2.2) ih

@[simp] theorem boundedSymbol?_terminal {g : IndexedGrammar T} {B : ℕ}
    (a : T) :
    boundedSymbol? (g := g) B (ISym.terminal a) = some (symbol.terminal a) := rfl

theorem boundedSymbol?_indexed_of_le {g : IndexedGrammar T} {B : ℕ}
    {A : g.nt} {σ : List g.flag} (hσ : σ.length ≤ B) :
    boundedSymbol? (g := g) B (ISym.indexed A σ) =
      some (symbol.nonterminal (A, ⟨σ, hσ⟩)) := by
  simp [boundedSymbol?, hσ]

theorem eraseBoundedSymbol_of_boundedSymbol? {g : IndexedGrammar T} {B : ℕ}
    {s : g.ISym} {s' : symbol T (BoundedStackNT g B)}
    (h : boundedSymbol? B s = some s') :
    eraseBoundedSymbol s' = s := by
  cases s with
  | terminal a =>
      simp [boundedSymbol?] at h
      subst s'
      rfl
  | indexed A σ =>
      simp only [boundedSymbol?] at h
      by_cases hσ : σ.length ≤ B
      · simp [hσ] at h
        subst s'
        rfl
      · simp [hσ] at h

theorem boundedSentential?_append {g : IndexedGrammar T} {B : ℕ}
    {u v : List g.ISym}
    {u' v' : List (symbol T (BoundedStackNT g B))}
    (hu : boundedSentential? B u = some u')
    (hv : boundedSentential? B v = some v') :
    boundedSentential? B (u ++ v) = some (u' ++ v') := by
  induction u generalizing u' with
  | nil =>
      simp [boundedSentential?] at hu
      subst u'
      simpa using hv
  | cons s u ih =>
      simp only [boundedSentential?] at hu ⊢
      cases hs : boundedSymbol? B s <;> simp [hs] at hu
      cases huTail : boundedSentential? B u <;> simp [huTail] at hu
      rename_i s' uTail
      cases hu
      simp [boundedSentential?, hs, ih huTail]

theorem eraseBoundedSentential_of_boundedSentential?
    {g : IndexedGrammar T} {B : ℕ}
    {w : List g.ISym} {w' : List (symbol T (BoundedStackNT g B))}
    (h : boundedSentential? B w = some w') :
    eraseBoundedSentential w' = w := by
  induction w generalizing w' with
  | nil =>
      simp [boundedSentential?] at h
      subst w'
      rfl
  | cons s w ih =>
      simp only [boundedSentential?] at h
      cases hs : boundedSymbol? B s <;> simp [hs] at h
      cases hw : boundedSentential? B w <;> simp [hw] at h
      rename_i s' tail
      rw [← h]
      simp [eraseBoundedSymbol_of_boundedSymbol? hs, ih hw]

@[simp] theorem boundedSentential?_map_terminal {g : IndexedGrammar T} {B : ℕ}
    (w : List T) :
    boundedSentential? (g := g) B
        (w.map fun a => (ISym.terminal a : g.ISym)) =
      some (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) := by
  induction w with
  | nil =>
      rfl
  | cons a w ih =>
      simp [boundedSentential?, ih]

theorem boundedSentential?_length {g : IndexedGrammar T} {B : ℕ}
    {w : List g.ISym} {w' : List (symbol T (BoundedStackNT g B))}
    (h : boundedSentential? B w = some w') :
    w'.length = w.length := by
  induction w generalizing w' with
  | nil =>
      simp [boundedSentential?] at h
      subst w'
      rfl
  | cons s w ih =>
      simp only [boundedSentential?] at h
      cases hs : boundedSymbol? B s <;> simp [hs] at h
      cases hw : boundedSentential? B w <;> simp [hw] at h
      rename_i s' tail
      rw [← h]
      simp [ih hw]

theorem exists_boundedSymbol?_of_stackHeight_le {g : IndexedGrammar T} {B : ℕ}
    {s : g.ISym} (hs : s.stackHeight ≤ B) :
    ∃ s' : symbol T (BoundedStackNT g B), boundedSymbol? B s = some s' := by
  cases s with
  | terminal a =>
      exact ⟨symbol.terminal a, rfl⟩
  | indexed A σ =>
      exact ⟨symbol.nonterminal (A, ⟨σ, by simpa using hs⟩),
        boundedSymbol?_indexed_of_le (g := g) (A := A) (σ := σ) (by simpa using hs)⟩

theorem exists_boundedSentential?_of_sententialMaxStackHeight_le
    {g : IndexedGrammar T} {B : ℕ} {w : List g.ISym}
    (hw : sententialMaxStackHeight w ≤ B) :
    ∃ w' : List (symbol T (BoundedStackNT g B)),
      boundedSentential? B w = some w' := by
  induction w with
  | nil =>
      exact ⟨[], rfl⟩
  | cons s w ih =>
      have hs : s.stackHeight ≤ B :=
        le_trans (Nat.le_max_left s.stackHeight (sententialMaxStackHeight w)) hw
      have hwTail : sententialMaxStackHeight w ≤ B :=
        le_trans (Nat.le_max_right s.stackHeight (sententialMaxStackHeight w)) hw
      obtain ⟨s', hs'⟩ := exists_boundedSymbol?_of_stackHeight_le (g := g) (B := B) hs
      obtain ⟨w', hw'⟩ := ih hwTail
      exact ⟨s' :: w', by simp [boundedSentential?, hs', hw']⟩

theorem sententialMaxStackHeight_le_of_append_left_le {g : IndexedGrammar T}
    {B : ℕ} {u v : List g.ISym}
    (h : sententialMaxStackHeight (u ++ v) ≤ B) :
    sententialMaxStackHeight u ≤ B := by
  have hmax : max (sententialMaxStackHeight u) (sententialMaxStackHeight v) ≤ B := by
    simpa using h
  exact le_trans (Nat.le_max_left _ _) hmax

theorem sententialMaxStackHeight_le_of_append_right_le {g : IndexedGrammar T}
    {B : ℕ} {u v : List g.ISym}
    (h : sententialMaxStackHeight (u ++ v) ≤ B) :
    sententialMaxStackHeight v ≤ B := by
  have hmax : max (sententialMaxStackHeight u) (sententialMaxStackHeight v) ≤ B := by
    simpa using h
  exact le_trans (Nat.le_max_right _ _) hmax

/-- Compile one indexed rule at one inherited stack into a bounded unrestricted rule, if both
the left-hand stack and every right-hand stack remain inside the bound. -/
def boundedRuleOf? {g : IndexedGrammar T} (B : ℕ)
    (r : IRule T g.nt g.flag) (σ : {σ : List g.flag // σ.length ≤ B}) :
    Option (grule T (BoundedStackNT g B)) :=
  match r.consume with
  | none =>
      match boundedSentential? B (g.expandRhs r.rhs σ.1) with
      | some out =>
          some
            { input_L := []
              input_N := (r.lhs, σ)
              input_R := []
              output_string := out }
      | none => none
  | some f =>
      if htop : σ.1.length < B then
        match boundedSentential? B (g.expandRhs r.rhs σ.1) with
        | some out =>
            some
              { input_L := []
                input_N := (r.lhs, ⟨f :: σ.1, by simpa using Nat.succ_le_iff.mpr htop⟩)
                input_R := []
                output_string := out }
        | none => none
      else
        none

/-- The compiled bounded rules of an indexed grammar. -/
noncomputable def boundedRules (g : IndexedGrammar T) [Fintype g.flag] (B : ℕ) :
    List (grule T (BoundedStackNT g B)) :=
  g.rules.flatMap fun r =>
    (boundedStacksList g B).filterMap fun σ => boundedRuleOf? B r σ

/-- The fixed-stack-bound unrestricted grammar associated to an indexed grammar. -/
noncomputable def boundedStackGrammar (g : IndexedGrammar T) [Fintype g.flag]
    (B : ℕ) : grammar T where
  nt := BoundedStackNT g B
  initial := (g.initial, ⟨[], by simp⟩)
  rules := boundedRules g B

theorem mem_boundedRules {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {br : grule T (BoundedStackNT g B)}
    (hbr : br ∈ boundedRules g B) :
    ∃ r ∈ g.rules, ∃ σ : {σ : List g.flag // σ.length ≤ B},
      boundedRuleOf? B r σ = some br := by
  classical
  rw [boundedRules, List.mem_flatMap] at hbr
  rcases hbr with ⟨r, hr, hbr⟩
  rw [List.mem_filterMap] at hbr
  rcases hbr with ⟨σ, _hσ, hσbr⟩
  exact ⟨r, hr, σ, hσbr⟩

theorem boundedRuleOf?_mem_boundedRules {g : IndexedGrammar T} [Fintype g.flag]
    {B : ℕ} {r : IRule T g.nt g.flag}
    {σ : {σ : List g.flag // σ.length ≤ B}}
    {br : grule T (BoundedStackNT g B)}
    (hr : r ∈ g.rules) (hbr : boundedRuleOf? B r σ = some br) :
    br ∈ boundedRules g B := by
  classical
  rw [boundedRules, List.mem_flatMap]
  refine ⟨r, hr, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨σ, mem_boundedStacksList σ, hbr⟩

theorem boundedRuleOf?_output_length {g : IndexedGrammar T} {B : ℕ}
    {r : IRule T g.nt g.flag} {σ : {σ : List g.flag // σ.length ≤ B}}
    {br : grule T (BoundedStackNT g B)}
    (hbr : boundedRuleOf? B r σ = some br) :
    br.output_string.length = r.rhs.length := by
  cases hc : r.consume with
  | none =>
      simp only [boundedRuleOf?, hc] at hbr
      cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
      | none =>
          simp [hout] at hbr
      | some out =>
          simp [hout] at hbr
          subst br
          simp [boundedSentential?_length hout, expandRhs_length]
  | some f =>
      simp only [boundedRuleOf?, hc] at hbr
      by_cases htop : σ.1.length < B
      · simp [htop] at hbr
        cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
        | none =>
            simp [hout] at hbr
        | some out =>
            simp [hout] at hbr
            subst br
            simp [boundedSentential?_length hout, expandRhs_length]
      · simp [htop] at hbr

theorem boundedRuleOf?_input_context_lengths {g : IndexedGrammar T} {B : ℕ}
    {r : IRule T g.nt g.flag} {σ : {σ : List g.flag // σ.length ≤ B}}
    {br : grule T (BoundedStackNT g B)}
    (hbr : boundedRuleOf? B r σ = some br) :
    br.input_L.length = 0 ∧ br.input_R.length = 0 := by
  cases hc : r.consume with
  | none =>
      simp only [boundedRuleOf?, hc] at hbr
      cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
      | none =>
          simp [hout] at hbr
      | some out =>
          simp [hout] at hbr
          subst br
          simp
  | some f =>
      simp only [boundedRuleOf?, hc] at hbr
      by_cases htop : σ.1.length < B
      · simp [htop] at hbr
        cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
        | none =>
            simp [hout] at hbr
        | some out =>
            simp [hout] at hbr
            subst br
            simp
      · simp [htop] at hbr

/-- Every rule of the fixed-stack-bound compilation of a normal-form indexed grammar is
noncontracting. -/
theorem boundedStackGrammar_noncontracting {g : IndexedGrammar T}
    [Fintype g.flag] [DecidableEq g.nt] {B : ℕ}
    (hNF : g.IsNormalForm) :
    grammar_noncontracting (boundedStackGrammar g B) := by
  intro br hbr
  rcases mem_boundedRules (g := g) (B := B) hbr with ⟨r, hr, σ, hσ⟩
  have hout := boundedRuleOf?_output_length (g := g) (B := B) hσ
  have hctx := boundedRuleOf?_input_context_lengths (g := g) (B := B) hσ
  have hnonempty := IRule.rhs_ne_nil_of_isNF (T := T)
    (N := g.nt) (F := g.flag) (r := r) (start := g.initial) (hNF r hr)
  have hpos : 1 ≤ r.rhs.length :=
    Nat.succ_le_of_lt (List.length_pos_of_ne_nil hnonempty)
  omega

/-- The fixed-stack-bound compilation of a normal-form indexed grammar is context-sensitive. -/
theorem is_CS_boundedStackGrammar_language {g : IndexedGrammar T}
    [Fintype g.flag] [DecidableEq g.nt] {B : ℕ}
    (hNF : g.IsNormalForm) :
    is_CS (grammar_language (boundedStackGrammar g B)) :=
  is_CS_of_is_noncontracting
    ⟨boundedStackGrammar g B, boundedStackGrammar_noncontracting hNF, rfl⟩

theorem boundedStackGrammar_transforms_of_indexed_transforms {g : IndexedGrammar T}
    [Fintype g.flag] {B : ℕ} {w₁ w₂ : List g.ISym}
    (hstep : g.Transforms w₁ w₂)
    (hw₁ : sententialMaxStackHeight w₁ ≤ B)
    (hw₂ : sententialMaxStackHeight w₂ ≤ B) :
    ∃ bw₁ bw₂ : List (symbol T (BoundedStackNT g B)),
      boundedSentential? B w₁ = some bw₁ ∧
      boundedSentential? B w₂ = some bw₂ ∧
      grammar_transforms (boundedStackGrammar g B) bw₁ bw₂ := by
  classical
  rcases hstep with ⟨r, u, v, σ, hr, hlhs, hrhs⟩
  cases hc : r.consume with
  | none =>
      simp only [hc] at hlhs
      have hinput : sententialMaxStackHeight (u ++ [ISym.indexed r.lhs σ] ++ v) ≤ B := by
        simpa [hlhs]
          using hw₁
      have hinput' : sententialMaxStackHeight (u ++ ([ISym.indexed r.lhs σ] ++ v)) ≤ B := by
        simpa [List.append_assoc] using hinput
      have huMax : sententialMaxStackHeight u ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := u) (v := [ISym.indexed r.lhs σ] ++ v) hinput'
      have hmidMax : sententialMaxStackHeight ([ISym.indexed r.lhs σ] ++ v) ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := u) (v := [ISym.indexed r.lhs σ] ++ v) hinput'
      have hsingleMax : sententialMaxStackHeight ([ISym.indexed r.lhs σ] : List g.ISym) ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := [ISym.indexed r.lhs σ]) (v := v) hmidMax
      have hvMax : sententialMaxStackHeight v ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := [ISym.indexed r.lhs σ]) (v := v) hmidMax
      have hσ : σ.length ≤ B := by
        simpa using hsingleMax
      have houtput : sententialMaxStackHeight (u ++ g.expandRhs r.rhs σ ++ v) ≤ B := by
        simpa [hrhs]
          using hw₂
      have houtput' : sententialMaxStackHeight (u ++ (g.expandRhs r.rhs σ ++ v)) ≤ B := by
        simpa [List.append_assoc] using houtput
      have houtMidMax : sententialMaxStackHeight (g.expandRhs r.rhs σ ++ v) ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := u) (v := g.expandRhs r.rhs σ ++ v) houtput'
      have houtMax : sententialMaxStackHeight (g.expandRhs r.rhs σ) ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := g.expandRhs r.rhs σ) (v := v) houtMidMax
      obtain ⟨bu, hbu⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) huMax
      obtain ⟨bv, hbv⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) hvMax
      obtain ⟨out, hout⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) houtMax
      let σb : {τ : List g.flag // τ.length ≤ B} := ⟨σ, hσ⟩
      let br : grule T (BoundedStackNT g B) :=
        { input_L := []
          input_N := (r.lhs, σb)
          input_R := []
          output_string := out }
      have hsingle :
          boundedSentential? B [ISym.indexed r.lhs σ] =
            some [symbol.nonterminal (r.lhs, σb)] := by
        simp [boundedSentential?, boundedSymbol?, σb, hσ]
      have hbrOf : boundedRuleOf? B r σb = some br := by
        simp [boundedRuleOf?, hc, hout, br, σb]
      have hbrMem : br ∈ (boundedStackGrammar g B).rules := by
        change br ∈ boundedRules g B
        exact boundedRuleOf?_mem_boundedRules (g := g) (B := B) hr hbrOf
      refine ⟨bu ++ [symbol.nonterminal (r.lhs, σb)] ++ bv, bu ++ out ++ bv, ?_, ?_, ?_⟩
      · rw [hlhs]
        have hmid := boundedSentential?_append (g := g) (B := B) hsingle hbv
        have hall := boundedSentential?_append (g := g) (B := B) hbu hmid
        simpa [List.append_assoc] using hall
      · rw [hrhs]
        have hmid := boundedSentential?_append (g := g) (B := B) hout hbv
        have hall := boundedSentential?_append (g := g) (B := B) hbu hmid
        simpa [List.append_assoc] using hall
      · refine ⟨br, hbrMem, bu, bv, ?_, ?_⟩
        · simp [br, List.append_assoc]
        · simp [br, List.append_assoc]
  | some f =>
      simp only [hc] at hlhs
      have hinput : sententialMaxStackHeight (u ++ [ISym.indexed r.lhs (f :: σ)] ++ v) ≤ B := by
        simpa [hlhs]
          using hw₁
      have hinput' :
          sententialMaxStackHeight (u ++ ([ISym.indexed r.lhs (f :: σ)] ++ v)) ≤ B := by
        simpa [List.append_assoc] using hinput
      have huMax : sententialMaxStackHeight u ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := u) (v := [ISym.indexed r.lhs (f :: σ)] ++ v) hinput'
      have hmidMax : sententialMaxStackHeight ([ISym.indexed r.lhs (f :: σ)] ++ v) ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := u) (v := [ISym.indexed r.lhs (f :: σ)] ++ v) hinput'
      have hsingleMax :
          sententialMaxStackHeight ([ISym.indexed r.lhs (f :: σ)] : List g.ISym) ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := [ISym.indexed r.lhs (f :: σ)]) (v := v) hmidMax
      have hvMax : sententialMaxStackHeight v ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := [ISym.indexed r.lhs (f :: σ)]) (v := v) hmidMax
      have hfσ : (f :: σ).length ≤ B := by
        simpa using hsingleMax
      have htop : σ.length < B :=
        Nat.lt_of_succ_le (by simpa using hfσ)
      have hσ : σ.length ≤ B :=
        le_of_lt htop
      have houtput : sententialMaxStackHeight (u ++ g.expandRhs r.rhs σ ++ v) ≤ B := by
        simpa [hrhs]
          using hw₂
      have houtput' : sententialMaxStackHeight (u ++ (g.expandRhs r.rhs σ ++ v)) ≤ B := by
        simpa [List.append_assoc] using houtput
      have houtMidMax : sententialMaxStackHeight (g.expandRhs r.rhs σ ++ v) ≤ B :=
        sententialMaxStackHeight_le_of_append_right_le
          (g := g) (u := u) (v := g.expandRhs r.rhs σ ++ v) houtput'
      have houtMax : sententialMaxStackHeight (g.expandRhs r.rhs σ) ≤ B :=
        sententialMaxStackHeight_le_of_append_left_le
          (g := g) (u := g.expandRhs r.rhs σ) (v := v) houtMidMax
      obtain ⟨bu, hbu⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) huMax
      obtain ⟨bv, hbv⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) hvMax
      obtain ⟨out, hout⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) houtMax
      let σb : {τ : List g.flag // τ.length ≤ B} := ⟨σ, hσ⟩
      let top : {τ : List g.flag // τ.length ≤ B} :=
        ⟨f :: σ, by simpa using Nat.succ_le_iff.mpr htop⟩
      let br : grule T (BoundedStackNT g B) :=
        { input_L := []
          input_N := (r.lhs, top)
          input_R := []
          output_string := out }
      have hsingle :
          boundedSentential? B [ISym.indexed r.lhs (f :: σ)] =
            some [symbol.nonterminal (r.lhs, top)] := by
        simp only [boundedSentential?]
        rw [show
          boundedSymbol? (g := g) B (ISym.indexed r.lhs (f :: σ)) =
            some (symbol.nonterminal (r.lhs, top)) by
            simpa [top] using
              boundedSymbol?_indexed_of_le (g := g) (B := B)
                (A := r.lhs) (σ := f :: σ) (by simpa using hfσ)]
      have hbrOf : boundedRuleOf? B r σb = some br := by
        simp [boundedRuleOf?, hc, htop, hout, br, top, σb]
      have hbrMem : br ∈ (boundedStackGrammar g B).rules := by
        change br ∈ boundedRules g B
        exact boundedRuleOf?_mem_boundedRules (g := g) (B := B) hr hbrOf
      refine ⟨bu ++ [symbol.nonterminal (r.lhs, top)] ++ bv, bu ++ out ++ bv, ?_, ?_, ?_⟩
      · rw [hlhs]
        have hmid := boundedSentential?_append (g := g) (B := B) hsingle hbv
        have hall := boundedSentential?_append (g := g) (B := B) hbu hmid
        simpa [List.append_assoc] using hall
      · rw [hrhs]
        have hmid := boundedSentential?_append (g := g) (B := B) hout hbv
        have hall := boundedSentential?_append (g := g) (B := B) hbu hmid
        simpa [List.append_assoc] using hall
      · refine ⟨br, hbrMem, bu, bv, ?_, ?_⟩
        · simp [br, List.append_assoc]
        · simp [br, List.append_assoc]

theorem indexed_transforms_of_boundedStackGrammar_transforms {g : IndexedGrammar T}
    [Fintype g.flag] {B : ℕ}
    {w₁ w₂ : List (symbol T (BoundedStackNT g B))}
    (hstep : grammar_transforms (boundedStackGrammar g B) w₁ w₂) :
    g.Transforms (eraseBoundedSentential w₁) (eraseBoundedSentential w₂) := by
  classical
  rcases hstep with ⟨br, hbr, u, v, hw₁, hw₂⟩
  change br ∈ boundedRules g B at hbr
  rcases mem_boundedRules (g := g) (B := B) hbr with ⟨r, hr, σ, hbrOf⟩
  cases hc : r.consume with
  | none =>
      simp only [boundedRuleOf?, hc] at hbrOf
      cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
      | none =>
          simp [hout] at hbrOf
      | some out =>
          simp [hout] at hbrOf
          subst br
          refine ⟨r, eraseBoundedSentential u, eraseBoundedSentential v, σ.1, hr, ?_, ?_⟩
          · simpa [eraseBoundedSentential, List.map_append, hc, List.append_assoc]
              using congrArg eraseBoundedSentential hw₁
          ·
            have houtErase := eraseBoundedSentential_of_boundedSentential? hout
            have houtErase' :
                List.map eraseBoundedSymbol out = g.expandRhs r.rhs σ.1 := by
              simpa [eraseBoundedSentential] using houtErase
            simpa [eraseBoundedSentential, List.map_append, houtErase', List.append_assoc]
              using congrArg eraseBoundedSentential hw₂
  | some f =>
      simp only [boundedRuleOf?, hc] at hbrOf
      by_cases htop : σ.1.length < B
      · simp [htop] at hbrOf
        cases hout : boundedSentential? B (g.expandRhs r.rhs σ.1) with
        | none =>
            simp [hout] at hbrOf
        | some out =>
            simp [hout] at hbrOf
            subst br
            refine ⟨r, eraseBoundedSentential u, eraseBoundedSentential v, σ.1, hr, ?_, ?_⟩
            · simpa [eraseBoundedSentential, List.map_append, hc, List.append_assoc]
                using congrArg eraseBoundedSentential hw₁
            ·
              have houtErase := eraseBoundedSentential_of_boundedSentential? hout
              have houtErase' :
                  List.map eraseBoundedSymbol out = g.expandRhs r.rhs σ.1 := by
                simpa [eraseBoundedSentential] using houtErase
              simpa [eraseBoundedSentential, List.map_append, houtErase', List.append_assoc]
                using congrArg eraseBoundedSentential hw₂
      · simp [htop] at hbrOf

theorem indexed_derives_of_boundedStackGrammar_derives {g : IndexedGrammar T}
    [Fintype g.flag] {B : ℕ}
    {w₁ w₂ : List (symbol T (BoundedStackNT g B))}
    (h : grammar_derives (boundedStackGrammar g B) w₁ w₂) :
    g.Derives (eraseBoundedSentential w₁) (eraseBoundedSentential w₂) := by
  induction h with
  | refl =>
      exact g.deri_self _
  | tail _ hstep ih =>
      exact ih.tail (indexed_transforms_of_boundedStackGrammar_transforms hstep)

theorem boundedStackGrammar_language_subset_language {g : IndexedGrammar T}
    [Fintype g.flag] {B : ℕ} :
    ∀ w, w ∈ grammar_language (boundedStackGrammar g B) → w ∈ g.Language := by
  intro w hw
  change g.Generates w
  have hder :=
    indexed_derives_of_boundedStackGrammar_derives
      (g := g) (B := B) (w₁ := [symbol.nonterminal (boundedStackGrammar g B).initial])
      (w₂ := w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)))
      (by simpa [grammar_language, grammar_generates] using hw)
  simpa [Generates, boundedStackGrammar] using hder

/-- Indexed derivations whose every displayed sentential form stays within a fixed stack
bound. This is the exact hypothesis needed by the bounded-stack compiler. -/
def StackBoundedDerivesIn (g : IndexedGrammar T) (B : ℕ) :
    ℕ → List g.ISym → List g.ISym → Prop
  | 0, w₁, w₂ => w₁ = w₂ ∧ sententialMaxStackHeight w₁ ≤ B
  | n + 1, w₁, w₂ =>
      ∃ w, StackBoundedDerivesIn g B n w₁ w ∧
        g.Transforms w w₂ ∧ sententialMaxStackHeight w₂ ≤ B

theorem StackBoundedDerivesIn.final_maxStackHeight_le {g : IndexedGrammar T}
    {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ B := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with ⟨rfl, hw₁⟩
      exact hw₁
  | succ n _ =>
      rcases h with ⟨_, _, _, hw₂⟩
      exact hw₂

theorem StackBoundedDerivesIn.initial_maxStackHeight_le {g : IndexedGrammar T}
    {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    sententialMaxStackHeight w₁ ≤ B := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with ⟨_, hw₁⟩
      exact hw₁
  | succ n ih =>
      rcases h with ⟨w, hprev, _, _⟩
      exact ih hprev

theorem StackBoundedDerivesIn.to_derivesIn {g : IndexedGrammar T}
    {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    g.DerivesIn n w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      exact h.1
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, _⟩
      exact ⟨w, ih hprev, hstep⟩

theorem StackBoundedDerivesIn.mono_bound {g : IndexedGrammar T}
    {B C n : ℕ} {w₁ w₂ : List g.ISym}
    (hBC : B ≤ C)
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    StackBoundedDerivesIn g C n w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with ⟨rfl, hw₁⟩
      exact ⟨rfl, le_trans hw₁ hBC⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hw₂⟩
      exact ⟨w, ih hprev, hstep, le_trans hw₂ hBC⟩

theorem StackBoundedDerivesIn.tail_of_transforms {g : IndexedGrammar T}
    {B n : ℕ} {w₁ w₂ w₃ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂)
    (hstep : g.Transforms w₂ w₃)
    (hw₃ : sententialMaxStackHeight w₃ ≤ B) :
    StackBoundedDerivesIn g B (n + 1) w₁ w₃ :=
  ⟨w₂, h, hstep, hw₃⟩

theorem StackBoundedDerivesIn.tail_of_transforms_isNormalForm_succ_bound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {w₁ w₂ w₃ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂)
    (hstep : g.Transforms w₂ w₃) :
    StackBoundedDerivesIn g (B + 1) (n + 1) w₁ w₃ := by
  have hpre : StackBoundedDerivesIn g (B + 1) n w₁ w₂ :=
    h.mono_bound (Nat.le_succ B)
  have hw₂ : sententialMaxStackHeight w₂ ≤ B :=
    h.final_maxStackHeight_le
  have hstepHeight :
      sententialMaxStackHeight w₃ ≤ sententialMaxStackHeight w₂ + 1 :=
    transforms_maxStackHeight_le_succ_of_isNormalForm hNF hstep
  exact hpre.tail_of_transforms hstep (by omega)

theorem exists_stackBoundedDerivesIn_tail_of_transforms_isNormalForm_succ_bound_le
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B i : ℕ} {w₁ w₂ w₃ : List g.ISym}
    (h : ∃ p : ℕ, p ≤ i ∧ StackBoundedDerivesIn g B p w₁ w₂)
    (hstep : g.Transforms w₂ w₃) :
    ∃ p : ℕ, p ≤ i + 1 ∧ StackBoundedDerivesIn g (B + 1) p w₁ w₃ := by
  obtain ⟨p, hpi, hpre⟩ := h
  exact ⟨p + 1, by omega,
    hpre.tail_of_transforms_isNormalForm_succ_bound hNF hstep⟩

theorem exists_stackBoundedDerivesIn_of_boundedStackGrammar_derives
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {w₁ w₂ : List (symbol T (BoundedStackNT g B))}
    (h : grammar_derives (boundedStackGrammar g B) w₁ w₂) :
    ∃ n, StackBoundedDerivesIn g B n
      (eraseBoundedSentential w₁) (eraseBoundedSentential w₂) := by
  induction h with
  | refl =>
      exact ⟨0, rfl, sententialMaxStackHeight_eraseBoundedSentential_le w₁⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hprev⟩
      exact ⟨n + 1, _, hprev,
        indexed_transforms_of_boundedStackGrammar_transforms hstep,
        sententialMaxStackHeight_eraseBoundedSentential_le _⟩

theorem exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
      trace.length = n + 1 ∧
      trace.head? = some w₁ ∧
      trace.getLast? = some w₂ ∧
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with ⟨rfl, hw₁⟩
      exact ⟨[w₁], by simp, by simp, by simp, by simp, by
        intro x hx
        have hx' : x = w₁ := by simpa using hx
        simpa [hx'] using hw₁⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hw₂⟩
      obtain ⟨trace, htrace, hlen, hhead, hlast, hbound⟩ := ih hprev
      refine ⟨trace ++ [w₂], ?_, ?_, ?_, ?_, ?_⟩
      · exact isDerivationTrace_append_step htrace hlast hstep
      · simp [hlen]
      ·
        have hne : trace ≠ [] := by
          intro hnil
          simp [hnil] at hlen
        simpa [List.head?_append_of_ne_nil trace hne] using hhead
      · simp
      ·
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hbound x hx
        ·
          have hx' : x = w₂ := by simpa using hx
          simpa [hx'] using hw₂

theorem stackBoundedDerivesIn_one_of_transforms {g : IndexedGrammar T}
    {B : ℕ} {w₁ w₂ : List g.ISym}
    (hstep : g.Transforms w₁ w₂)
    (hw₁ : sententialMaxStackHeight w₁ ≤ B)
    (hw₂ : sententialMaxStackHeight w₂ ≤ B) :
    StackBoundedDerivesIn g B 1 w₁ w₂ :=
  ⟨w₁, ⟨rfl, hw₁⟩, hstep, hw₂⟩

theorem stackBoundedDerivesIn_binary_context_of_rule {g : IndexedGrammar T}
    {B : ℕ} {A C D : g.nt} {σ : List g.flag} {r : IRule T g.nt g.flag}
    {u v : List g.ISym}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none, IRhsSymbol.nonterminal D none])
    (hstart : sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) ≤ B)
    (hfinal : sententialMaxStackHeight
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) ≤ B) :
    StackBoundedDerivesIn g B 1
      (u ++ [ISym.indexed A σ] ++ v)
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) :=
  stackBoundedDerivesIn_one_of_transforms
    (NFYield.transforms_binary_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hstart hfinal

theorem stackBoundedDerivesIn_pop_context_of_rule {g : IndexedGrammar T}
    {B : ℕ} {A C : g.nt} {f : g.flag} {ρ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none])
    (hstart : sententialMaxStackHeight (u ++ [ISym.indexed A (f :: ρ)] ++ v) ≤ B)
    (hfinal : sententialMaxStackHeight (u ++ [ISym.indexed C ρ] ++ v) ≤ B) :
    StackBoundedDerivesIn g B 1
      (u ++ [ISym.indexed A (f :: ρ)] ++ v)
      (u ++ [ISym.indexed C ρ] ++ v) :=
  stackBoundedDerivesIn_one_of_transforms
    (NFYield.transforms_pop_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hstart hfinal

theorem stackBoundedDerivesIn_push_context_of_rule {g : IndexedGrammar T}
    {B : ℕ} {A C : g.nt} {f : g.flag} {σ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C (some f)])
    (hstart : sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) ≤ B)
    (hfinal : sententialMaxStackHeight (u ++ [ISym.indexed C (f :: σ)] ++ v) ≤ B) :
    StackBoundedDerivesIn g B 1
      (u ++ [ISym.indexed A σ] ++ v)
      (u ++ [ISym.indexed C (f :: σ)] ++ v) :=
  stackBoundedDerivesIn_one_of_transforms
    (NFYield.transforms_push_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hstart hfinal

theorem stackBoundedDerivesIn_terminal_context_of_rule {g : IndexedGrammar T}
    {B : ℕ} {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a])
    (hstart : sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) ≤ B)
    (hfinal : sententialMaxStackHeight (u ++ [ISym.terminal a] ++ v) ≤ B) :
    StackBoundedDerivesIn g B 1
      (u ++ [ISym.indexed A σ] ++ v)
      (u ++ [ISym.terminal a] ++ v) :=
  stackBoundedDerivesIn_one_of_transforms
    (NFYield.transforms_terminal_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hstart hfinal

theorem StackBoundedDerivesIn.tail_binary_context_of_rule {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C D : g.nt} {σ : List g.flag} {r : IRule T g.nt g.flag}
    {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none, IRhsSymbol.nonterminal D none])
    (hfinal : sententialMaxStackHeight
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) ≤ B) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) :=
  hpre.tail_of_transforms
    (NFYield.transforms_binary_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hfinal

theorem StackBoundedDerivesIn.tail_pop_context_of_rule {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C : g.nt} {f : g.flag} {ρ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A (f :: ρ)] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none])
    (hfinal : sententialMaxStackHeight (u ++ [ISym.indexed C ρ] ++ v) ≤ B) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.indexed C ρ] ++ v) :=
  hpre.tail_of_transforms
    (NFYield.transforms_pop_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hfinal

theorem StackBoundedDerivesIn.tail_push_context_of_rule {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C : g.nt} {f : g.flag} {σ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C (some f)])
    (hfinal : sententialMaxStackHeight (u ++ [ISym.indexed C (f :: σ)] ++ v) ≤ B) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.indexed C (f :: σ)] ++ v) :=
  hpre.tail_of_transforms
    (NFYield.transforms_push_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hfinal

theorem StackBoundedDerivesIn.tail_terminal_context_of_rule {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a])
    (hfinal : sententialMaxStackHeight (u ++ [ISym.terminal a] ++ v) ≤ B) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.terminal a] ++ v) :=
  hpre.tail_of_transforms
    (NFYield.transforms_terminal_context_of_rule
      (g := g) (u := u) (v := v) hr hlhs hc hrhs)
    hfinal

theorem StackBoundedDerivesIn.tail_binary_context_same_bound_of_rule
    {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C D : g.nt} {σ : List g.flag} {r : IRule T g.nt g.flag}
    {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none, IRhsSymbol.nonterminal D none]) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) := by
  have hfinal : sententialMaxStackHeight
      (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v) ≤ B := by
    rw [sententialMaxStackHeight_context_binary_eq (A := A)]
    exact hpre.final_maxStackHeight_le
  exact hpre.tail_binary_context_of_rule hr hlhs hc hrhs hfinal

theorem StackBoundedDerivesIn.tail_pop_context_same_bound_of_rule
    {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C : g.nt} {f : g.flag} {ρ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A (f :: ρ)] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C none]) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.indexed C ρ] ++ v) := by
  have hfinal : sententialMaxStackHeight (u ++ [ISym.indexed C ρ] ++ v) ≤ B :=
    le_trans sententialMaxStackHeight_context_pop_le hpre.final_maxStackHeight_le
  exact hpre.tail_pop_context_of_rule hr hlhs hc hrhs hfinal

theorem StackBoundedDerivesIn.tail_push_context_succ_bound_of_rule
    {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A C : g.nt} {f : g.flag} {σ : List g.flag}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal C (some f)]) :
    StackBoundedDerivesIn g (B + 1) (n + 1) first
      (u ++ [ISym.indexed C (f :: σ)] ++ v) := by
  have hpre' : StackBoundedDerivesIn g (B + 1) n first
      (u ++ [ISym.indexed A σ] ++ v) :=
    hpre.mono_bound (Nat.le_succ B)
  have hfinal :
      sententialMaxStackHeight (u ++ [ISym.indexed C (f :: σ)] ++ v) ≤ B + 1 :=
    le_trans sententialMaxStackHeight_context_push_le_succ
      (Nat.add_le_add_right hpre.final_maxStackHeight_le 1)
  exact hpre'.tail_push_context_of_rule hr hlhs hc hrhs hfinal

theorem StackBoundedDerivesIn.tail_terminal_context_same_bound_of_rule
    {g : IndexedGrammar T}
    {B n : ℕ} {first : List g.ISym}
    {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag} {u v : List g.ISym}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    StackBoundedDerivesIn g B (n + 1) first
      (u ++ [ISym.terminal a] ++ v) := by
  have hfinal : sententialMaxStackHeight (u ++ [ISym.terminal a] ++ v) ≤ B :=
    le_trans sententialMaxStackHeight_context_terminal_le hpre.final_maxStackHeight_le
  exact hpre.tail_terminal_context_of_rule hr hlhs hc hrhs hfinal

theorem StackBoundedDerivesIn.tail_of_NFYield_context {g : IndexedGrammar T}
    {B n : ℕ} {first u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    {w : List T}
    (hpre : StackBoundedDerivesIn g B n first (u ++ [ISym.indexed A σ] ++ v))
    (hcert : NFYield g A σ w) :
    (∃ C D : g.nt, ∃ x y : List T, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal C none, IRhsSymbol.nonterminal D none] ∧
        w = x ++ y ∧
        NFYield g C σ x ∧
        NFYield g D σ y ∧
        StackBoundedDerivesIn g B (n + 1) first
          (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v)) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ C : g.nt, ∃ r ∈ g.rules,
      σ = f :: ρ ∧
        r.lhs = A ∧ r.consume = some f ∧
        r.rhs = [IRhsSymbol.nonterminal C none] ∧
        NFYield g C ρ w ∧
        StackBoundedDerivesIn g B (n + 1) first
          (u ++ [ISym.indexed C ρ] ++ v)) ∨
    (∃ C : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal C (some f)] ∧
        NFYield g C (f :: σ) w ∧
        StackBoundedDerivesIn g (B + 1) (n + 1) first
          (u ++ [ISym.indexed C (f :: σ)] ++ v)) ∨
    (∃ a : T, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.terminal a] ∧
        w = [a] ∧
        StackBoundedDerivesIn g B (n + 1) first
          (u ++ [ISym.terminal a] ++ v)) := by
  cases hcert with
  | binary hr hlhs hc hrhs hleft hright =>
      left
      refine ⟨_, _, _, _, _, hr, hlhs, hc, hrhs, rfl, hleft, hright, ?_⟩
      exact hpre.tail_binary_context_same_bound_of_rule hr hlhs hc hrhs
  | pop hr hlhs hc hrhs hrest =>
      right
      left
      refine ⟨_, _, _, _, hr, rfl, hlhs, hc, hrhs, hrest, ?_⟩
      exact hpre.tail_pop_context_same_bound_of_rule hr hlhs hc hrhs
  | push hr hlhs hc hrhs hrest =>
      right
      right
      left
      refine ⟨_, _, _, hr, hlhs, hc, hrhs, hrest, ?_⟩
      exact hpre.tail_push_context_succ_bound_of_rule hr hlhs hc hrhs
  | terminal hr hlhs hc hrhs =>
      right
      right
      right
      refine ⟨_, _, hr, hlhs, hc, hrhs, rfl, ?_⟩
      exact hpre.tail_terminal_context_same_bound_of_rule hr hlhs hc hrhs

theorem exists_stackBoundedDerivesIn_tail_of_NFYield_context_le
    {g : IndexedGrammar T}
    {B i : ℕ} {first u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    {w : List T}
    (hpre : ∃ p : ℕ,
      p ≤ i ∧ StackBoundedDerivesIn g B p first (u ++ [ISym.indexed A σ] ++ v))
    (hcert : NFYield g A σ w) :
    (∃ C D : g.nt, ∃ x y : List T, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal C none, IRhsSymbol.nonterminal D none] ∧
        w = x ++ y ∧
        NFYield g C σ x ∧
        NFYield g D σ y ∧
        ∃ p : ℕ,
          p ≤ i + 1 ∧
            StackBoundedDerivesIn g B p first
              (u ++ [ISym.indexed C σ, ISym.indexed D σ] ++ v)) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ C : g.nt, ∃ r ∈ g.rules,
      σ = f :: ρ ∧
        r.lhs = A ∧ r.consume = some f ∧
        r.rhs = [IRhsSymbol.nonterminal C none] ∧
        NFYield g C ρ w ∧
        ∃ p : ℕ,
          p ≤ i + 1 ∧
            StackBoundedDerivesIn g B p first
              (u ++ [ISym.indexed C ρ] ++ v)) ∨
    (∃ C : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal C (some f)] ∧
        NFYield g C (f :: σ) w ∧
        ∃ p : ℕ,
          p ≤ i + 1 ∧
            StackBoundedDerivesIn g (B + 1) p first
              (u ++ [ISym.indexed C (f :: σ)] ++ v)) ∨
    (∃ a : T, ∃ r ∈ g.rules,
      r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.terminal a] ∧
        w = [a] ∧
        ∃ p : ℕ,
          p ≤ i + 1 ∧
            StackBoundedDerivesIn g B p first
              (u ++ [ISym.terminal a] ++ v)) := by
  obtain ⟨p, hpi, hpre⟩ := hpre
  rcases hpre.tail_of_NFYield_context hcert with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨C, D, x, y, r, hr, hlhs, hc, hrhs, hw, hleft, hright, htail⟩
    left
    refine ⟨C, D, x, y, r, hr, hlhs, hc, hrhs, hw, hleft, hright, p + 1, ?_, htail⟩
    omega
  · rcases hpop with ⟨f, ρ, C, r, hr, hσ, hlhs, hc, hrhs, hchild, htail⟩
    right
    left
    refine ⟨f, ρ, C, r, hr, hσ, hlhs, hc, hrhs, hchild, p + 1, ?_, htail⟩
    omega
  · rcases hpush with ⟨C, f, r, hr, hlhs, hc, hrhs, hchild, htail⟩
    right
    right
    left
    refine ⟨C, f, r, hr, hlhs, hc, hrhs, hchild, p + 1, ?_, htail⟩
    omega
  · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, htail⟩
    right
    right
    right
    refine ⟨a, r, hr, hlhs, hc, hrhs, hw, p + 1, ?_, htail⟩
    omega

theorem stackBoundedDerivesIn_trans {g : IndexedGrammar T}
    {B m n : ℕ} {w₁ w₂ w₃ : List g.ISym}
    (h₁ : StackBoundedDerivesIn g B m w₁ w₂)
    (h₂ : StackBoundedDerivesIn g B n w₂ w₃) :
    StackBoundedDerivesIn g B (m + n) w₁ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      rcases h₂ with ⟨rfl, _⟩
      simpa using h₁
  | succ n ih =>
      rcases h₂ with ⟨w, hprev, hstep, hw₃⟩
      rw [Nat.add_succ]
      exact ⟨w, ih hprev, hstep, hw₃⟩

theorem stackBoundedDerivesIn_of_bounded_isDerivationTrace
    {g : IndexedGrammar T} {B n : ℕ} {trace : List (List g.ISym)}
    {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B) :
    StackBoundedDerivesIn g B n w₁ w₂ := by
  induction n generalizing trace w₁ w₂ with
  | zero =>
      cases trace with
      | nil => simp at hlen
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hhead hlast
              subst a
              subst w₂
              exact ⟨rfl, hbound w₁ (by simp)⟩
          | cons b rest =>
              simp at hlen
  | succ n ih =>
      cases trace with
      | nil => simp at hlen
      | cons a rest =>
          cases rest with
          | nil => simp at hlen
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have ha : a = w₁ := by simpa using hhead
              subst a
              have hlen_tail : (b :: rest).length = n + 1 := by
                simpa using hlen
              have hlast_tail : (b :: rest).getLast? = some w₂ := by
                simpa using hlast
              have hbound_tail : ∀ x ∈ b :: rest, sententialMaxStackHeight x ≤ B := by
                intro x hx
                exact hbound x (by simp [hx])
              have htail : StackBoundedDerivesIn g B n b w₂ :=
                ih htrace.2 hlen_tail (by simp) hlast_tail hbound_tail
              have hw₁ : sententialMaxStackHeight w₁ ≤ B :=
                hbound w₁ (by simp)
              have hb : sententialMaxStackHeight b ≤ B :=
                hbound b (by simp)
              have hone : StackBoundedDerivesIn g B 1 w₁ b :=
                stackBoundedDerivesIn_one_of_transforms htrace.1 hw₁ hb
              simpa [Nat.add_comm] using stackBoundedDerivesIn_trans hone htail

theorem stackBoundedDerivesIn_trace_prefix
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hbound : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    StackBoundedDerivesIn g B i first (trace.get ⟨i, hi⟩) := by
  induction i with
  | zero =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          have ha : a = first := by simpa using hhead
          subst a
          exact ⟨rfl, by simpa using hbound 0 hi⟩
  | succ i ih =>
      have hiPrev : i < trace.length := by omega
      have hprev : StackBoundedDerivesIn g B i first (trace.get ⟨i, hiPrev⟩) :=
        ih hiPrev
      have hstep : g.Transforms (trace.get ⟨i, hiPrev⟩) (trace.get ⟨i + 1, hi⟩) :=
        isDerivationTrace_get_transform htrace hi
      have hone :
          StackBoundedDerivesIn g B 1
            (trace.get ⟨i, hiPrev⟩) (trace.get ⟨i + 1, hi⟩) :=
        stackBoundedDerivesIn_one_of_transforms hstep
          (hbound i hiPrev) (hbound (i + 1) hi)
      exact stackBoundedDerivesIn_trans hprev hone

/-- Prefix-bounded variant of `stackBoundedDerivesIn_trace_prefix`. Only the displayed prefix
through `i` has to satisfy the stack bound. -/
theorem stackBoundedDerivesIn_trace_prefix_of_prefix_bound
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ}
    (hbound : ∀ j (hj : j < trace.length),
      j ≤ i → sententialMaxStackHeight (trace.get ⟨j, hj⟩) ≤ B)
    (hi : i < trace.length) :
    StackBoundedDerivesIn g B i first (trace.get ⟨i, hi⟩) := by
  induction i with
  | zero =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          have ha : a = first := by simpa using hhead
          subst a
          exact ⟨rfl, by simpa using hbound 0 hi (by omega)⟩
  | succ i ih =>
      have hiPrev : i < trace.length := by omega
      have hprev : StackBoundedDerivesIn g B i first (trace.get ⟨i, hiPrev⟩) :=
        ih (fun j hj hji => hbound j hj (Nat.le_trans hji (Nat.le_succ i))) hiPrev
      have hstep : g.Transforms (trace.get ⟨i, hiPrev⟩) (trace.get ⟨i + 1, hi⟩) :=
        isDerivationTrace_get_transform htrace hi
      have hone :
          StackBoundedDerivesIn g B 1
            (trace.get ⟨i, hiPrev⟩) (trace.get ⟨i + 1, hi⟩) :=
        stackBoundedDerivesIn_one_of_transforms hstep
          (hbound i hiPrev (Nat.le_succ i)) (hbound (i + 1) hi le_rfl)
      exact stackBoundedDerivesIn_trans hprev hone

/-- A repeated finite surface gives a shortened bounded prefix to the later surface erasure,
provided the earlier prefix is already stack-bounded by the surface height. This is the direct
reachability fact used when a later high-stack configuration repeats an earlier bounded
surface. -/
theorem exists_stackBoundedDerivesIn_erase_later_surface_of_repeated_surface_prefix_bound
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i j : ℕ} (hi : i < trace.length) (hj : j < trace.length)
    (_hij : i ≤ j)
    (hbound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B (trace.get ⟨j, hj⟩)) :
    ∃ p : ℕ,
      p ≤ i ∧
        StackBoundedDerivesIn g B p first
          (eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get ⟨j, hj⟩))) := by
  refine ⟨i, le_rfl, ?_⟩
  have hpre :
      StackBoundedDerivesIn g B i first (trace.get ⟨i, hi⟩) :=
    stackBoundedDerivesIn_trace_prefix_of_prefix_bound
      (g := g) (B := B) htrace hhead hbound hi
  have hiErase :
      eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩)) =
        trace.get ⟨i, hi⟩ :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      (hbound i hi (by omega))
  have herase := congrArg eraseSurfaceForm hsurface
  rw [hiErase] at herase
  rw [herase] at hpre
  simpa using hpre

theorem exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {first ys : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ} (hi : i < trace.length)
    (hbound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hys : sententialMaxStackHeight ys ≤ B)
    (hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B ys) :
    ∃ p : ℕ,
      p ≤ i ∧ StackBoundedDerivesIn g B p first ys := by
  refine ⟨i, le_rfl, ?_⟩
  have hpre :
      StackBoundedDerivesIn g B i first (trace.get ⟨i, hi⟩) :=
    stackBoundedDerivesIn_trace_prefix_of_prefix_bound
      (g := g) (B := B) htrace hhead hbound hi
  have hiErase :
      eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩)) =
        trace.get ⟨i, hi⟩ :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      (hbound i hi (by omega))
  have hysErase :
      eraseSurfaceForm (surfaceOfTruncatedForm B ys) = ys :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le hys
  have herase := congrArg eraseSurfaceForm hsurface
  rw [hiErase, hysErase] at herase
  rw [herase] at hpre
  simpa using hpre

theorem exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound_le
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {first ys : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i j : ℕ} (hi : i < trace.length) (hij : i ≤ j)
    (hbound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hys : sententialMaxStackHeight ys ≤ B)
    (hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B ys) :
    ∃ p : ℕ,
      p ≤ j ∧ StackBoundedDerivesIn g B p first ys := by
  obtain ⟨p, hpi, hpre⟩ :=
    exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound
      (g := g) (B := B) htrace hhead hi hbound hys hsurface
  exact ⟨p, le_trans hpi hij, hpre⟩

theorem exists_stackBoundedDerivesIn_canonical_context_of_surface_eq_prefix_bound_le
    {g : IndexedGrammar T} {B P K : ℕ} {trace : List (List g.ISym)}
    {first u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i j : ℕ} (hi : i < trace.length) (hij : i ≤ j)
    (hbound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hctx : sententialMaxStackHeight (u ++ v) ≤ B)
    (hPK : P + K ≤ B)
    (hτ : τ.length ≤ K)
    (hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) :
    ∃ p : ℕ,
      p ≤ j ∧
        StackBoundedDerivesIn g B p first
          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  have hys :
      sententialMaxStackHeight (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ≤ B :=
    sententialMaxStackHeight_context_indexed_take_append_le hctx hPK hτ
  exact
    exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound_le
      (g := g) (B := B) htrace hhead hi hij hbound hys hsurface

/-- Prefix-local target-compatible pigeonhole packaged with bounded reachability. If the
target-compatible bounded-surface frontier is smaller than the displayed prefix of an accepting
trace, then some repeated surface inside that prefix yields a shortened bounded derivation from
the initial form to the later surface erasure. -/
theorem exists_stackBoundedDerivesIn_erase_repeated_targetCompatible_surface_before_of_card_lt
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B m : ℕ} {trace : List (List g.ISym)} {w : List T}
    {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        m + 1)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) :
    ∃ i j : Fin trace.length, i < j ∧ j.1 ≤ m ∧
      ∃ p : ℕ,
        p ≤ i.1 ∧
          StackBoundedDerivesIn g B p first
            (eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get j))) := by
  obtain ⟨i, j, hij, hjm, hsurface⟩ :=
    accepting_derivationTrace_exists_targetCompatible_surface_repeat_before_of_card_lt
      (g := g) hNF htrace hlast hm hcard
  have hijNat : i.1 ≤ j.1 := Nat.le_of_lt (show i.1 < j.1 from hij)
  have him : i.1 ≤ m := le_trans hijNat hjm
  have hprefixBoundI : ∀ k (hk : k < trace.length),
      k ≤ i.1 → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B := by
    intro k hk hki
    exact hprefixBound k hk (le_trans hki him)
  obtain ⟨p, hpj, hpre⟩ :=
    exists_stackBoundedDerivesIn_erase_later_surface_of_repeated_surface_prefix_bound
      (g := g) (B := B) htrace hhead i.2 j.2 hijNat hprefixBoundI hsurface
  exact ⟨i, j, hij, hjm, p, hpj, hpre⟩

/-- Interval-local target-compatible pigeonhole packaged with bounded reachability. The
repeated surface is found inside `[a, m]`, and the bounded prefix reaches the later surface
erasure no later than the earlier repeated index. -/
theorem exists_stackBoundedDerivesIn_erase_repeated_targetCompatible_surface_between_of_card_lt
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B a m : ℕ} {trace : List (List g.ISym)} {w : List T}
    {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (ham : a ≤ m)
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        m + 1 - a)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) :
    ∃ i j : Fin trace.length, i < j ∧ a ≤ i.1 ∧ j.1 ≤ m ∧
      ∃ p : ℕ,
        p ≤ i.1 ∧
          StackBoundedDerivesIn g B p first
            (eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get j))) := by
  obtain ⟨i, j, hij, hai, hjm, hsurface⟩ :=
    accepting_derivationTrace_exists_targetCompatible_surface_repeat_between_of_card_lt
      (g := g) hNF htrace hlast ham hm hcard
  have hijNat : i.1 ≤ j.1 := Nat.le_of_lt (show i.1 < j.1 from hij)
  have him : i.1 ≤ m := le_trans hijNat hjm
  have hprefixBoundI : ∀ k (hk : k < trace.length),
      k ≤ i.1 → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B := by
    intro k hk hki
    exact hprefixBound k hk (le_trans hki him)
  obtain ⟨p, hpi, hpre⟩ :=
    exists_stackBoundedDerivesIn_erase_later_surface_of_repeated_surface_prefix_bound
      (g := g) (B := B) htrace hhead i.2 j.2 hijNat hprefixBoundI hsurface
  exact ⟨i, j, hij, hai, hjm, p, hpi, hpre⟩

theorem stackBoundedDerivesIn_trace_suffix
    {g : IndexedGrammar T} {B : ℕ} {trace : List (List g.ISym)}
    {last : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some last)
    (hbound : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    StackBoundedDerivesIn g B (trace.length - 1 - i) (trace.get ⟨i, hi⟩) last := by
  have hdropTrace : IsDerivationTrace g (trace.drop i) :=
    isDerivationTrace_drop htrace i
  have hdropLen : (trace.drop i).length = (trace.length - 1 - i) + 1 := by
    rw [List.length_drop]
    omega
  have hdropHead : (trace.drop i).head? = some (trace.get ⟨i, hi⟩) :=
    trace_drop_head?_eq_get (g := g) hi
  have hdropLast : (trace.drop i).getLast? = some last := by
    rw [trace_drop_getLast?_eq_getLast? (g := g) hi, hlast]
  have hboundMem : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
    intro x hx
    rcases (List.mem_iff_get.mp hx) with ⟨j, hj⟩
    rw [← hj]
    exact hbound j.1 j.2
  have hdropBound : ∀ x ∈ trace.drop i, sententialMaxStackHeight x ≤ B := by
    intro x hx
    exact hboundMem x ((List.drop_sublist i trace).subset hx)
  exact stackBoundedDerivesIn_of_bounded_isDerivationTrace
    hdropTrace hdropLen hdropHead hdropLast hdropBound

theorem minimal_accepting_stackBound_le_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} {n B C m : ℕ} {w : List T}
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? = some (w.map ISym.terminal) ∧
          ∀ i (hi : i < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ C') →
        B ≤ C')
    (hbounded : StackBoundedDerivesIn g C m
      [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmn : m ≤ n) :
    B ≤ C := by
  have hder_m :
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) :=
    StackBoundedDerivesIn.to_derivesIn hbounded
  have hn_le_m : n ≤ m := hminLength m hder_m
  have hm_eq : m = n := by omega
  subst m
  obtain ⟨trace', htrace', hlen', hhead', hlast', hbound'⟩ :=
    exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn hbounded
  exact hminBound C
    ⟨trace', htrace', hlen', hhead', hlast', by
      intro i hi
      exact hbound' (trace'.get ⟨i, hi⟩) (List.get_mem trace' ⟨i, hi⟩)⟩

theorem minimal_accepting_stackBound_le_of_stackBounded_prefix_suffix
    {g : IndexedGrammar T} {n B Bpre Bsuf p q : ℕ} {w : List T}
    {mid : List g.ISym}
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? = some (w.map ISym.terminal) ∧
          ∀ i (hi : i < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ C') →
        B ≤ C')
    (hpre : StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []] mid)
    (hsuf : StackBoundedDerivesIn g Bsuf q mid (w.map ISym.terminal))
    (hsteps : p + q ≤ n) :
    B ≤ max Bpre Bsuf := by
  have hpre' :
      StackBoundedDerivesIn g (max Bpre Bsuf) p [ISym.indexed g.initial []] mid :=
    StackBoundedDerivesIn.mono_bound (Nat.le_max_left Bpre Bsuf) hpre
  have hsuf' :
      StackBoundedDerivesIn g (max Bpre Bsuf) q mid (w.map ISym.terminal) :=
    StackBoundedDerivesIn.mono_bound (Nat.le_max_right Bpre Bsuf) hsuf
  exact minimal_accepting_stackBound_le_of_stackBoundedDerivesIn
    hminLength hminBound (stackBoundedDerivesIn_trans hpre' hsuf') hsteps

theorem stackBoundedDerivesIn_append_left {g : IndexedGrammar T}
    {B n : ℕ} {u u' v : List g.ISym}
    (h : StackBoundedDerivesIn g B n u u')
    (hv : sententialMaxStackHeight v ≤ B) :
    StackBoundedDerivesIn g B n (u ++ v) (u' ++ v) := by
  induction n generalizing u' with
  | zero =>
      rcases h with ⟨rfl, hu⟩
      exact ⟨rfl, by simpa using max_le hu hv⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hu'⟩
      exact ⟨w ++ v, ih hprev, transforms_append_left hstep v,
        by simpa using max_le hu' hv⟩

theorem stackBoundedDerivesIn_append_right {g : IndexedGrammar T}
    {B n : ℕ} {u v v' : List g.ISym}
    (h : StackBoundedDerivesIn g B n v v')
    (hu : sententialMaxStackHeight u ≤ B) :
    StackBoundedDerivesIn g B n (u ++ v) (u ++ v') := by
  induction n generalizing v' with
  | zero =>
      rcases h with ⟨rfl, hv⟩
      exact ⟨rfl, by simpa using max_le hu hv⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hv'⟩
      exact ⟨u ++ w, ih hprev, transforms_append_right hstep u,
        by simpa using max_le hu hv'⟩

theorem stackBoundedDerivesIn_append {g : IndexedGrammar T}
    {B m n : ℕ} {u u' v v' : List g.ISym}
    (hu : StackBoundedDerivesIn g B m u u')
    (hv : StackBoundedDerivesIn g B n v v') :
    StackBoundedDerivesIn g B (m + n) (u ++ v) (u' ++ v') :=
  stackBoundedDerivesIn_trans
    (stackBoundedDerivesIn_append_left hu
      (StackBoundedDerivesIn.initial_maxStackHeight_le hv))
    (stackBoundedDerivesIn_append_right hv
      (StackBoundedDerivesIn.final_maxStackHeight_le hu))

theorem stackBoundedDerivesIn_append_to_terminals_of_stackBoundedDerivesIn
    {g : IndexedGrammar T}
    {B m n : ℕ} {u v : List g.ISym} {wu wv : List T}
    (hu : StackBoundedDerivesIn g B m u
      (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hv : StackBoundedDerivesIn g B n v
      (wv.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g B (m + n) (u ++ v)
      ((wu ++ wv).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa [List.map_append] using stackBoundedDerivesIn_append hu hv

/-- Bounded terminal-word composition from a positionwise list of singleton derivations. -/
theorem stackBoundedDerivesIn_symbols_to_terminals_of_forall₂
    {g : IndexedGrammar T} {B : ℕ}
    {xs : List g.ISym} {parts : List (ℕ × List T)}
    (hparts : List.Forall₂
      (fun s p => StackBoundedDerivesIn g B p.1 [s]
        (p.2.map fun a => (ISym.terminal a : g.ISym)))
      xs parts) :
    StackBoundedDerivesIn g B ((parts.map fun p => p.1).sum) xs
      ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  induction hparts with
  | nil =>
      simp [StackBoundedDerivesIn]
  | cons hhead _htail ih =>
      have hcomp :=
        stackBoundedDerivesIn_append_to_terminals_of_stackBoundedDerivesIn
          (g := g) hhead ih
      simpa [List.map_append] using hcomp

theorem stackBoundedDerivesIn_pair_to_terminals_of_stackBoundedDerivesIn
    {g : IndexedGrammar T}
    {B m n : ℕ} {A C : g.nt} {σ τ : List g.flag} {u v : List T}
    (hleft : StackBoundedDerivesIn g B m [ISym.indexed A σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : StackBoundedDerivesIn g B n [ISym.indexed C τ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g B (m + n) [ISym.indexed A σ, ISym.indexed C τ]
      ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    stackBoundedDerivesIn_append_to_terminals_of_stackBoundedDerivesIn
      (g := g) (u := [ISym.indexed A σ]) (v := [ISym.indexed C τ])
      hleft hright

theorem stackBoundedDerivesIn_binary_rule_to_terminals_of_children
    {g : IndexedGrammar T}
    {K m n : ℕ} {A B C : g.nt} {τ : List g.flag} {u v w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (hw : w = u ++ v)
    (hτ : τ.length ≤ K)
    (hleft : StackBoundedDerivesIn g K m [ISym.indexed B τ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : StackBoundedDerivesIn g K n [ISym.indexed C τ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g K (1 + (m + n)) [ISym.indexed A τ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  subst w
  have hstep :
      g.Transforms [ISym.indexed A τ] [ISym.indexed B τ, ISym.indexed C τ] := by
    refine ⟨r, [], [], τ, hr, ?_, ?_⟩
    · simp [hc, hlhs]
    · simp [hrhs, expandRhs]
  have hstart : sententialMaxStackHeight ([ISym.indexed A τ] : List g.ISym) ≤ K := by
    simpa using hτ
  have hmid :
      sententialMaxStackHeight ([ISym.indexed B τ, ISym.indexed C τ] : List g.ISym) ≤ K := by
    simpa using max_le hτ hτ
  have hfirst :=
    stackBoundedDerivesIn_one_of_transforms (g := g) hstep hstart hmid
  have hchildren :=
    stackBoundedDerivesIn_pair_to_terminals_of_stackBoundedDerivesIn
      (g := g) hleft hright
  simpa [List.map_append] using stackBoundedDerivesIn_trans hfirst hchildren

theorem stackBoundedDerivesIn_pop_rule_to_terminals_of_child
    {g : IndexedGrammar T}
    {K n : ℕ} {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hρtop : (f :: ρ).length ≤ K)
    (hchild : StackBoundedDerivesIn g K n [ISym.indexed B ρ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g K (1 + n) [ISym.indexed A (f :: ρ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hstep : g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] := by
    refine ⟨r, [], [], ρ, hr, ?_, ?_⟩
    · simp [hc, hlhs]
    · simp [hrhs, expandRhs]
  have hstart :
      sententialMaxStackHeight ([ISym.indexed A (f :: ρ)] : List g.ISym) ≤ K := by
    simpa using hρtop
  have hρ : ρ.length ≤ K :=
    le_trans (Nat.le_succ ρ.length) (by simpa using hρtop)
  have hmid : sententialMaxStackHeight ([ISym.indexed B ρ] : List g.ISym) ≤ K := by
    simpa using hρ
  have hfirst :=
    stackBoundedDerivesIn_one_of_transforms (g := g) hstep hstart hmid
  simpa using stackBoundedDerivesIn_trans hfirst hchild

theorem stackBoundedDerivesIn_push_rule_to_terminals_of_child
    {g : IndexedGrammar T}
    {K n : ℕ} {A B : g.nt} {f : g.flag} {τ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (hτtop : (f :: τ).length ≤ K)
    (hchild : StackBoundedDerivesIn g K n [ISym.indexed B (f :: τ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g K (1 + n) [ISym.indexed A τ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hstep : g.Transforms [ISym.indexed A τ] [ISym.indexed B (f :: τ)] := by
    refine ⟨r, [], [], τ, hr, ?_, ?_⟩
    · simp [hc, hlhs]
    · simp [hrhs, expandRhs]
  have hτ : τ.length ≤ K :=
    le_trans (Nat.le_succ τ.length) (by simpa using hτtop)
  have hstart : sententialMaxStackHeight ([ISym.indexed A τ] : List g.ISym) ≤ K := by
    simpa using hτ
  have hmid :
      sententialMaxStackHeight ([ISym.indexed B (f :: τ)] : List g.ISym) ≤ K := by
    simpa using hτtop
  have hfirst :=
    stackBoundedDerivesIn_one_of_transforms (g := g) hstep hstart hmid
  simpa using stackBoundedDerivesIn_trans hfirst hchild

theorem stackBoundedDerivesIn_terminal_rule
    {g : IndexedGrammar T}
    {K : ℕ} {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a])
    (hσ : σ.length ≤ K) :
    StackBoundedDerivesIn g K 1 [ISym.indexed A σ]
      ([a].map fun b => (ISym.terminal b : g.ISym)) := by
  have hstep : g.Transforms [ISym.indexed A σ] [ISym.terminal a] := by
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · simp [hc, hlhs]
    · simp [hrhs, expandRhs]
  have hstart : sententialMaxStackHeight ([ISym.indexed A σ] : List g.ISym) ≤ K := by
    simpa using hσ
  have hfinal : sententialMaxStackHeight ([ISym.terminal a] : List g.ISym) ≤ K := by
    simp
  simpa using stackBoundedDerivesIn_one_of_transforms (g := g) hstep hstart hfinal

theorem NFYield.StackBounded.exists_stackBoundedDerivesIn
    {g : IndexedGrammar T} {K : ℕ}
    {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield.StackBounded g K A σ w) :
    ∃ n,
      StackBoundedDerivesIn g K n [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
  induction h with
  | binary hσ hr hlhs hc hrhs _ _ ihleft ihright =>
      rcases ihleft with ⟨m, hleft⟩
      rcases ihright with ⟨n, hright⟩
      exact ⟨1 + (m + n),
        stackBoundedDerivesIn_binary_rule_to_terminals_of_children
          (g := g) hr hlhs hc hrhs rfl hσ hleft hright⟩
  | pop hσ hr hlhs hc hrhs _ ihrest =>
      rcases ihrest with ⟨n, hrest⟩
      exact ⟨1 + n,
        stackBoundedDerivesIn_pop_rule_to_terminals_of_child
          (g := g) hr hlhs hc hrhs hσ hrest⟩
  | push _ hr hlhs hc hrhs hrest ihrest =>
      rcases ihrest with ⟨n, hrestBounded⟩
      exact ⟨1 + n,
        stackBoundedDerivesIn_push_rule_to_terminals_of_child
          (g := g) hr hlhs hc hrhs
          (NFYield.StackBounded.stack_length_le hrest) hrestBounded⟩
  | terminal hσ hr hlhs hc hrhs =>
      exact ⟨1,
        stackBoundedDerivesIn_terminal_rule
          (g := g) hr hlhs hc hrhs hσ⟩

/-- A stack-bounded singleton derivation in normal form has a bounded parse certificate.
The certificate bound is stated as `B + n`, using the certificate extractor's linear
count-bound. -/
theorem NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (h : StackBoundedDerivesIn g B n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    NFYield.StackBounded g (B + n) A σ w := by
  have hσ : σ.length ≤ B := by
    simpa using StackBoundedDerivesIn.initial_maxStackHeight_le h
  exact NFYield.stackBounded_of_derivesIn_isNormalForm_initial_stackBound
    (g := g) hNF hσ (StackBoundedDerivesIn.to_derivesIn h)

theorem stackBoundedDerivesIn_binary_rule_to_terminals_of_prefixed_children
    {g : IndexedGrammar T}
    {M m n : ℕ} {A B C : g.nt} {pref τ : List g.flag} {u v w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (hw : w = u ++ v)
    (hτ : τ.length ≤ M)
    (hleft : StackBoundedDerivesIn g (pref.length + M) m
      [ISym.indexed B (pref ++ τ)]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : StackBoundedDerivesIn g (pref.length + M) n
      [ISym.indexed C (pref ++ τ)]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (pref.length + M) (1 + (m + n))
      [ISym.indexed A (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hstack : (pref ++ τ).length ≤ pref.length + M := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_binary_rule_to_terminals_of_children
    (g := g) (K := pref.length + M) (A := A) (B := B) (C := C)
    (τ := pref ++ τ) (u := u) (v := v) (w := w)
    hr hlhs hc hrhs hw hstack hleft hright

theorem stackBoundedDerivesIn_pop_rule_to_terminals_of_prefixed_child
    {g : IndexedGrammar T}
    {M n : ℕ} {A B : g.nt} {f : g.flag} {pref τ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hτ : τ.length ≤ M)
    (hchild : StackBoundedDerivesIn g (pref.length + M + 1) n
      [ISym.indexed B (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (pref.length + M + 1) (1 + n)
      [ISym.indexed A (f :: (pref ++ τ))]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have htop : (f :: (pref ++ τ)).length ≤ pref.length + M + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_pop_rule_to_terminals_of_child
    (g := g) (K := pref.length + M + 1) (A := A) (B := B) (f := f)
    (ρ := pref ++ τ) (w := w) hr hlhs hc hrhs htop hchild

theorem stackBoundedDerivesIn_push_rule_to_terminals_of_prefixed_child
    {g : IndexedGrammar T}
    {M n : ℕ} {A B : g.nt} {f : g.flag} {pref τ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (hτ : τ.length ≤ M)
    (hchild : StackBoundedDerivesIn g (pref.length + M + 1) n
      [ISym.indexed B (f :: (pref ++ τ))]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (pref.length + M + 1) (1 + n)
      [ISym.indexed A (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have htop : (f :: (pref ++ τ)).length ≤ pref.length + M + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_push_rule_to_terminals_of_child
    (g := g) (K := pref.length + M + 1) (A := A) (B := B) (f := f)
    (τ := pref ++ τ) (w := w) hr hlhs hc hrhs htop hchild

theorem stackBoundedDerivesIn_terminal_rule_of_prefixed_stack
    {g : IndexedGrammar T}
    {M : ℕ} {A : g.nt} {pref τ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a])
    (hτ : τ.length ≤ M) :
    StackBoundedDerivesIn g (pref.length + M) 1
      [ISym.indexed A (pref ++ τ)]
      ([a].map fun b => (ISym.terminal b : g.ISym)) := by
  have hstack : (pref ++ τ).length ≤ pref.length + M := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_terminal_rule
    (g := g) (K := pref.length + M) (A := A) (σ := pref ++ τ) (a := a)
    hr hlhs hc hrhs hstack

theorem stackBoundedDerivesIn_binary_rule_to_terminals_of_bounded_prefix_children
    {g : IndexedGrammar T}
    {N K m n : ℕ} {A B C : g.nt} {pref τ : List g.flag} {u v w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (hw : w = u ++ v)
    (hpref : pref.length ≤ N)
    (hτ : τ.length ≤ K)
    (hleft : StackBoundedDerivesIn g (N + K + 1) m
      [ISym.indexed B (pref ++ τ)]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : StackBoundedDerivesIn g (N + K + 1) n
      [ISym.indexed C (pref ++ τ)]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (N + K + 1) (1 + (m + n))
      [ISym.indexed A (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hstack : (pref ++ τ).length ≤ N + K + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_binary_rule_to_terminals_of_children
    (g := g) (K := N + K + 1) (A := A) (B := B) (C := C)
    (τ := pref ++ τ) (u := u) (v := v) (w := w)
    hr hlhs hc hrhs hw hstack hleft hright

theorem stackBoundedDerivesIn_pop_rule_to_terminals_of_bounded_prefix_child
    {g : IndexedGrammar T}
    {N K n : ℕ} {A B : g.nt} {f : g.flag} {pref τ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hpref : pref.length ≤ N)
    (hτ : τ.length ≤ K)
    (hchild : StackBoundedDerivesIn g (N + K + 1) n
      [ISym.indexed B (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (N + K + 1) (1 + n)
      [ISym.indexed A (f :: (pref ++ τ))]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have htop : (f :: (pref ++ τ)).length ≤ N + K + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_pop_rule_to_terminals_of_child
    (g := g) (K := N + K + 1) (A := A) (B := B) (f := f)
    (ρ := pref ++ τ) (w := w) hr hlhs hc hrhs htop hchild

theorem stackBoundedDerivesIn_push_rule_to_terminals_of_bounded_prefix_child
    {g : IndexedGrammar T}
    {N K n : ℕ} {A B : g.nt} {f : g.flag} {pref τ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (hpref : pref.length ≤ N)
    (hτ : τ.length ≤ K)
    (hchild : StackBoundedDerivesIn g (N + K + 1) n
      [ISym.indexed B (f :: (pref ++ τ))]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (N + K + 1) (1 + n)
      [ISym.indexed A (pref ++ τ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have htop : (f :: (pref ++ τ)).length ≤ N + K + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_push_rule_to_terminals_of_child
    (g := g) (K := N + K + 1) (A := A) (B := B) (f := f)
    (τ := pref ++ τ) (w := w) hr hlhs hc hrhs htop hchild

theorem stackBoundedDerivesIn_terminal_rule_of_bounded_prefix_stack
    {g : IndexedGrammar T}
    {N K : ℕ} {A : g.nt} {pref τ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a])
    (hpref : pref.length ≤ N)
    (hτ : τ.length ≤ K) :
    StackBoundedDerivesIn g (N + K + 1) 1
      [ISym.indexed A (pref ++ τ)]
      ([a].map fun b => (ISym.terminal b : g.ISym)) := by
  have hstack : (pref ++ τ).length ≤ N + K + 1 := by
    simp [List.length_append]
    omega
  exact stackBoundedDerivesIn_terminal_rule
    (g := g) (K := N + K + 1) (A := A) (σ := pref ++ τ) (a := a)
    hr hlhs hc hrhs hstack

/-- Convert an ordinary counted derivation into a stack-bounded counted derivation when every
intermediate sentential form is known to satisfy the same stack bound. -/
theorem stackBoundedDerivesIn_of_derivesIn_of_intermediate_stackBound
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂)
    (hstack : ∀ i x, DerivesInIntermediate g n w₁ w₂ i x →
      sententialMaxStackHeight x ≤ B) :
    StackBoundedDerivesIn g B n w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      have hmid : DerivesInIntermediate g 0 w₁ w₁ 0 w₁ := by
        exact ⟨le_rfl, rfl, rfl⟩
      exact ⟨rfl, hstack 0 w₁ hmid⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprevStack : ∀ i x, DerivesInIntermediate g n w₁ w i x →
          sententialMaxStackHeight x ≤ B := by
        intro i x hmid
        rcases hmid with ⟨hi, hpre, hsuf⟩
        refine hstack i x ?_
        refine ⟨le_trans hi (Nat.le_succ n), hpre, ?_⟩
        have htail : g.DerivesIn ((n - i) + 1) x w₂ :=
          ⟨w, hsuf, hstep⟩
        have hsub : n + 1 - i = (n - i) + 1 := by omega
        simpa [hsub] using htail
      have hfull : g.DerivesIn (n + 1) w₁ w₂ := ⟨w, hprev, hstep⟩
      have hw₂ : sententialMaxStackHeight w₂ ≤ B := by
        exact hstack (n + 1) w₂ ⟨le_rfl, hfull, by simp⟩
      exact ⟨w, ih hprev hprevStack, hstep, hw₂⟩

theorem stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂)
    (hstart : sententialMaxStackHeight w₁ ≤ B) :
    StackBoundedDerivesIn g (B + n) n w₁ w₂ := by
  apply stackBoundedDerivesIn_of_derivesIn_of_intermediate_stackBound
    (g := g) (B := B + n) h
  intro i x hmid
  have hx :=
    derivesIn_maxStackHeight_le_add_of_isNormalForm
      (g := g) hNF hmid.2.1
  have hi : i ≤ n := hmid.1
  omega

theorem stackBoundedDerivesIn_of_accepting_derivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g n n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  apply stackBoundedDerivesIn_of_derivesIn_of_intermediate_stackBound
    (g := g) (B := n) h
  intro i x hmid
  exact le_trans
    (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)
    hmid.1

theorem stackBoundedDerivesIn_of_accepting_derivesIn_isNormalForm_steps_le
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {N n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (hn : n ≤ N) :
    StackBoundedDerivesIn g N n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)) :=
  StackBoundedDerivesIn.mono_bound hn
    (stackBoundedDerivesIn_of_accepting_derivesIn_isNormalForm hNF h)

/-- In normal form, a positionwise split of a terminal suffix gives a bounded derivation of
the whole sentential form. The bound is the surface stack bound plus the total remaining
rewrite budget. -/
theorem stackBoundedDerivesIn_symbols_to_terminals_of_forall₂_derivesIn_isNormalForm_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B₀ : ℕ} {xs : List g.ISym} {parts : List (ℕ × List T)}
    (hparts : List.Forall₂
      (fun s p => g.DerivesIn p.1 [s]
        (p.2.map fun a => (ISym.terminal a : g.ISym)))
      xs parts)
    (hheight : ∀ s ∈ xs, s.stackHeight ≤ B₀) :
    StackBoundedDerivesIn g (B₀ + (parts.map fun p => p.1).sum)
      ((parts.map fun p => p.1).sum) xs
      ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  induction hparts with
  | nil =>
      simp [StackBoundedDerivesIn]
  | cons hhead _htail ih =>
      rename_i s p xs parts
      have hstart : sententialMaxStackHeight ([s] : List g.ISym) ≤ B₀ := by
        simpa using hheight s (by simp)
      have hheadBound₀ :
          StackBoundedDerivesIn g (B₀ + p.1) p.1 [s]
            (p.2.map fun a => (ISym.terminal a : g.ISym)) :=
        stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
          (g := g) (B := B₀) hNF hhead hstart
      have hheadBound :
          StackBoundedDerivesIn g (B₀ + (((p :: parts).map fun p => p.1).sum)) p.1 [s]
            (p.2.map fun a => (ISym.terminal a : g.ISym)) :=
        StackBoundedDerivesIn.mono_bound (by simp) hheadBound₀
      have htailHeight : ∀ t ∈ xs, t.stackHeight ≤ B₀ := by
        intro t ht
        exact hheight t (by simp [ht])
      have htailBound₀ :
          StackBoundedDerivesIn g (B₀ + (parts.map fun p => p.1).sum)
            ((parts.map fun p => p.1).sum) xs
            ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) :=
        ih htailHeight
      have htailBound :
          StackBoundedDerivesIn g (B₀ + (((p :: parts).map fun p => p.1).sum))
            ((parts.map fun p => p.1).sum) xs
            ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) :=
        StackBoundedDerivesIn.mono_bound (by simp) htailBound₀
      have hcomp :=
        stackBoundedDerivesIn_append_to_terminals_of_stackBoundedDerivesIn
          (g := g) hheadBound htailBound
      simpa [List.map_append] using hcomp

/-- Whole-form bounded suffix extracted from an accepting trace position. The proof uses the
positionwise terminal-yield split, so the bound is distributed over every live symbol rather
than over a distinguished local occurrence. -/
theorem stackBoundedDerivesIn_accepting_derivationTrace_symbols_suffix_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hi : i < trace.length) :
    StackBoundedDerivesIn g
      (sententialMaxStackHeight (trace.get ⟨i, hi⟩) + (trace.length - 1 - i))
      (trace.length - 1 - i)
      (trace.get ⟨i, hi⟩)
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨parts, _hlen, hsum, hflat, hparts⟩ :=
    accepting_derivationTrace_symbols_suffix_to_terminals_split
      (g := g) htrace hlast hi
  have hheight :
      ∀ s ∈ trace.get ⟨i, hi⟩,
        s.stackHeight ≤ sententialMaxStackHeight (trace.get ⟨i, hi⟩) := by
    intro s hs
    exact stackHeight_le_sententialMaxStackHeight_of_mem hs
  have hbounded :=
    stackBoundedDerivesIn_symbols_to_terminals_of_forall₂_derivesIn_isNormalForm_stackBound
      (g := g) hNF hparts hheight
  simpa [hsum, hflat] using hbounded

theorem minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n B Bpre p q : ℕ} {w : List T} {mid : List g.ISym}
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? = some (w.map ISym.terminal) ∧
          ∀ i (hi : i < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ C') →
        B ≤ C')
    (hpre : StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []] mid)
    (hsuf : g.DerivesIn q mid (w.map ISym.terminal))
    (hsteps : p + q ≤ n) :
    B ≤ Bpre + q := by
  have hmidBound : sententialMaxStackHeight mid ≤ Bpre :=
    StackBoundedDerivesIn.final_maxStackHeight_le hpre
  have hsufBounded :
      StackBoundedDerivesIn g (Bpre + q) q mid (w.map ISym.terminal) :=
    stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
      (g := g) (B := Bpre) hNF hsuf hmidBound
  have hpreBounded :
      StackBoundedDerivesIn g (Bpre + q) p [ISym.indexed g.initial []] mid :=
    StackBoundedDerivesIn.mono_bound (by omega) hpre
  exact minimal_accepting_stackBound_le_of_stackBoundedDerivesIn
    hminLength hminBound
    (stackBoundedDerivesIn_trans hpreBounded hsufBounded) hsteps

theorem minimal_accepting_stackBound_le_of_reachable_trace_suffix_derivesIn
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n B Bpre q : ℕ} {w : List T} {trace : List (List g.ISym)}
    {i : ℕ} {mid : List g.ISym}
    (hlen : trace.length = n + 1)
    (hi : i < trace.length)
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? = some (w.map ISym.terminal) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hpre : StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []] mid)
    (hsuf : g.DerivesIn q mid (w.map ISym.terminal))
    (hq : q ≤ trace.length - 1 - i) :
    B ≤ Bpre + q := by
  have hsteps : i + q ≤ n := by omega
  exact minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
    (g := g) hNF hminLength hminBound hpre hsuf hsteps

/-- A prefix-local target-compatible surface repeat gives an explicit least-stack-bound
upper bound for a shortest accepting trace. The bounded prefix reaches the later erased
surface in no more than the earlier index, while the original suffix from the earlier
configuration finishes the derivation. -/
theorem exists_minimal_stackBound_le_of_targetCompatible_surface_repeat_prefix_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K m n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g target K)).card <
        m + 1)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K) :
    ∃ i j : Fin trace.length, i < j ∧ j.1 ≤ m ∧
      B ≤ K + (trace.length - 1 - i.1) := by
  obtain ⟨i, j, hij, hjm, hsurface⟩ :=
    accepting_derivationTrace_exists_targetCompatible_surface_repeat_before_of_card_lt
      (g := g) hNF htrace hlast hm hcard
  have hijNat : i.1 ≤ j.1 := Nat.le_of_lt (show i.1 < j.1 from hij)
  have him : i.1 ≤ m := le_trans hijNat hjm
  have hprefixBoundI : ∀ k (hk : k < trace.length),
      k ≤ i.1 → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K := by
    intro k hk hki
    exact hprefixBound k hk (le_trans hki him)
  obtain ⟨p, hpi, hpreSurface⟩ :=
    exists_stackBoundedDerivesIn_erase_later_surface_of_repeated_surface_prefix_bound
      (g := g) (B := K) htrace hhead i.2 j.2 hijNat hprefixBoundI hsurface
  have hiErase :
      eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get i)) = trace.get i :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      (hprefixBound i.1 i.2 him)
  have herase :
      trace.get i =
        eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)) := by
    have hcongr := congrArg eraseSurfaceForm hsurface
    rwa [hiErase] at hcongr
  have hsuffix_i :
      g.DerivesIn (trace.length - 1 - i.1) (trace.get i)
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast i.2
  have hsuffix :
      g.DerivesIn (trace.length - 1 - i.1)
        (eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)))
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    rw [← herase]
    exact hsuffix_i
  have hsteps : p + (trace.length - 1 - i.1) ≤ n := by
    omega
  have hB :
      B ≤ K + (trace.length - 1 - i.1) :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := K) (p := p)
      (q := trace.length - 1 - i.1) (w := target)
      (mid := eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)))
      hminLength hminBound hpreSurface hsuffix hsteps
  exact ⟨i, j, hij, hjm, hB⟩

/-- Interval-local version of
`exists_minimal_stackBound_le_of_targetCompatible_surface_repeat_prefix_bound`. The repeated
surface is found in `[a, m]`, so the resulting upper bound also records that the suffix starts
at or after `a`. -/
theorem exists_minimal_stackBound_le_of_targetCompatible_surface_repeat_interval_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K a m n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (ham : a ≤ m)
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g target K)).card <
        m + 1 - a)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K) :
    ∃ i j : Fin trace.length, i < j ∧ a ≤ i.1 ∧ j.1 ≤ m ∧
      B ≤ K + (trace.length - 1 - i.1) := by
  obtain ⟨i, j, hij, hai, hjm, hsurface⟩ :=
    accepting_derivationTrace_exists_targetCompatible_surface_repeat_between_of_card_lt
      (g := g) hNF htrace hlast ham hm hcard
  have hijNat : i.1 ≤ j.1 := Nat.le_of_lt (show i.1 < j.1 from hij)
  have him : i.1 ≤ m := le_trans hijNat hjm
  have hprefixBoundI : ∀ k (hk : k < trace.length),
      k ≤ i.1 → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K := by
    intro k hk hki
    exact hprefixBound k hk (le_trans hki him)
  obtain ⟨p, hpi, hpreSurface⟩ :=
    exists_stackBoundedDerivesIn_erase_later_surface_of_repeated_surface_prefix_bound
      (g := g) (B := K) htrace hhead i.2 j.2 hijNat hprefixBoundI hsurface
  have hiErase :
      eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get i)) = trace.get i :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      (hprefixBound i.1 i.2 him)
  have herase :
      trace.get i =
        eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)) := by
    have hcongr := congrArg eraseSurfaceForm hsurface
    rwa [hiErase] at hcongr
  have hsuffix_i :
      g.DerivesIn (trace.length - 1 - i.1) (trace.get i)
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast i.2
  have hsuffix :
      g.DerivesIn (trace.length - 1 - i.1)
        (eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)))
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    rw [← herase]
    exact hsuffix_i
  have hsteps : p + (trace.length - 1 - i.1) ≤ n := by
    omega
  have hB :
      B ≤ K + (trace.length - 1 - i.1) :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := K) (p := p)
      (q := trace.length - 1 - i.1) (w := target)
      (mid := eraseSurfaceForm (surfaceOfTruncatedForm K (trace.get j)))
      hminLength hminBound hpreSurface hsuffix hsteps
  exact ⟨i, j, hij, hai, hjm, hB⟩

/-- If the least stack bound of the chosen shortest accepting trace is larger than `K + N`,
then every `K`-bounded interval whose positions all have suffix budget at most `N` has length
bounded by the finite target-compatible surface frontier. Otherwise the interval-local
pigeonhole/splicing lemma would build an accepting trace with stack bound at most `K + N`,
contradicting minimality of `B`. -/
theorem targetCompatible_surface_interval_length_le_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K N a m n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (ham : a ≤ m)
    (hm : m < trace.length)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hsuffixBudget : ∀ i : Fin trace.length,
      a ≤ i.1 → trace.length - 1 - i.1 ≤ N)
    (hgt : K + N < B) :
    m + 1 - a ≤
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g target K)).card := by
  apply le_of_not_gt
  intro hcard
  obtain ⟨i, _j, _hij, hai, _hjm, hB⟩ :=
    exists_minimal_stackBound_le_of_targetCompatible_surface_repeat_interval_bound
      (g := g) hNF htrace hlen hhead hlast hminLength hminBound
      ham hm hcard hprefixBound
  have hB_le :
      B ≤ K + N := by
    exact le_trans hB (Nat.add_le_add_left (hsuffixBudget i hai) K)
  exact (not_lt_of_ge hB_le) hgt

/-- Late-window specialization of
`targetCompatible_surface_interval_length_le_card_of_minimal_stack_gt_bound`. Starting the
interval at `trace.length - 1 - N` makes the suffix budget automatic for every position in
the interval. -/
theorem targetCompatible_late_surface_interval_length_le_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K N m n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (ha : trace.length - 1 - N ≤ m)
    (hm : m < trace.length)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ m → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hgt : K + N < B) :
    m + 1 - (trace.length - 1 - N) ≤
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g target K)).card := by
  exact targetCompatible_surface_interval_length_le_card_of_minimal_stack_gt_bound
    (g := g) hNF htrace hlen hhead hlast hminLength hminBound
    (a := trace.length - 1 - N) (m := m) ha hm hprefixBound
    (fun i hi => by omega) hgt

/-- If the least accepting stack bound is larger than `K + N`, then some configuration in the
finite late window of length `|targetCompatibleBoundedSurfaceForms g target K| + 1` already
exceeds stack height `K`. Otherwise that whole window would be `K`-bounded, contradicting the
late-window surface-repeat bound. -/
theorem exists_high_stack_before_late_surface_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K N n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hm :
      trace.length - 1 - N +
        (Set.Finite.toFinset
          (targetCompatibleBoundedSurfaceForms_finite g target K)).card <
        trace.length)
    (hgt : K + N < B) :
    ∃ k : Fin trace.length,
      k.1 ≤
          trace.length - 1 - N +
            (Set.Finite.toFinset
              (targetCompatibleBoundedSurfaceForms_finite g target K)).card ∧
        K < sententialMaxStackHeight (trace.get k) := by
  classical
  let a := trace.length - 1 - N
  let C :=
    (Set.Finite.toFinset
      (targetCompatibleBoundedSurfaceForms_finite g target K)).card
  have hm' : a + C < trace.length := by
    simpa [a, C] using hm
  by_contra hnone
  have hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ a + C → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K := by
    intro k hk hkm
    by_contra hle
    have hhigh : K < sententialMaxStackHeight (trace.get ⟨k, hk⟩) :=
      Nat.lt_of_not_ge hle
    exact hnone ⟨⟨k, hk⟩, by simpa [a, C] using hkm, hhigh⟩
  have hwindow :
      (a + C) + 1 - a ≤ C := by
    simpa [a, C] using
      (targetCompatible_late_surface_interval_length_le_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := K) (N := N) (m := a + C) (n := n) (B := B)
        (by dsimp [a]; omega) hm' hprefixBound hgt)
  have hsucc : C + 1 ≤ C := by
    omega
  omega

/-- Sharpened late-window locator. If the prefix before `trace.length - 1 - N` is already
`K`-bounded and the least accepting stack bound is larger than `K + N`, then the forced
high-stack configuration occurs inside the late window itself. This is the form whose witness
also has suffix budget at most `N`. -/
theorem exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K N n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hbeforeBound : ∀ k (hk : k < trace.length),
      k < trace.length - 1 - N →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hm :
      trace.length - 1 - N +
        (Set.Finite.toFinset
          (targetCompatibleBoundedSurfaceForms_finite g target K)).card <
        trace.length)
    (hgt : K + N < B) :
    ∃ k : Fin trace.length,
      trace.length - 1 - N ≤ k.1 ∧
        k.1 ≤
          trace.length - 1 - N +
            (Set.Finite.toFinset
              (targetCompatibleBoundedSurfaceForms_finite g target K)).card ∧
        trace.length - 1 - k.1 ≤ N ∧
        K < sententialMaxStackHeight (trace.get k) := by
  classical
  let a := trace.length - 1 - N
  let C :=
    (Set.Finite.toFinset
      (targetCompatibleBoundedSurfaceForms_finite g target K)).card
  have hm' : a + C < trace.length := by
    simpa [a, C] using hm
  by_contra hnone
  have hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ a + C → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K := by
    intro k hk hkm
    by_cases hka : k < a
    · exact hbeforeBound k hk (by simpa [a] using hka)
    · have hak : a ≤ k := Nat.le_of_not_gt hka
      apply le_of_not_gt
      intro hhigh
      exact hnone ⟨⟨k, hk⟩, by simpa [a] using hak, by simpa [a, C] using hkm,
        by
          have ha' : trace.length - 1 - N ≤ k := by
            simpa [a] using hak
          have hsum : trace.length - 1 ≤ N + k := by
            have hsum' : trace.length - 1 ≤ k + N :=
              (Nat.sub_le_iff_le_add).mp ha'
            simpa [Nat.add_comm] using hsum'
          exact (Nat.sub_le_iff_le_add).mpr hsum,
        hhigh⟩
  have hwindow :
      (a + C) + 1 - a ≤ C := by
    simpa [a, C] using
      (targetCompatible_late_surface_interval_length_le_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := K) (N := N) (m := a + C) (n := n) (B := B)
        (by dsimp [a]; omega) hm' hprefixBound hgt)
  have hsucc : C + 1 ≤ C := by
    omega
  omega

/-- Cardinal-budget dichotomy for the sharpened late-window locator. With `N` instantiated as
the target-compatible surface-cardinality, either the chosen shortest derivation already has
fewer steps than that finite cardinality, or the late window fits and contains a high-stack
configuration with that same suffix budget. -/
theorem exists_high_stack_between_late_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hbeforeBound : ∀ k (hk : k < trace.length),
      k < trace.length - 1 -
          (Set.Finite.toFinset
            (targetCompatibleBoundedSurfaceForms_finite g target K)).card →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hgt :
      K +
          (Set.Finite.toFinset
            (targetCompatibleBoundedSurfaceForms_finite g target K)).card <
        B) :
    n <
        (Set.Finite.toFinset
          (targetCompatibleBoundedSurfaceForms_finite g target K)).card ∨
      ∃ k : Fin trace.length,
        trace.length - 1 -
            (Set.Finite.toFinset
              (targetCompatibleBoundedSurfaceForms_finite g target K)).card ≤ k.1 ∧
          k.1 ≤
            trace.length - 1 -
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target K)).card +
              (Set.Finite.toFinset
                (targetCompatibleBoundedSurfaceForms_finite g target K)).card ∧
          trace.length - 1 - k.1 ≤
            (Set.Finite.toFinset
              (targetCompatibleBoundedSurfaceForms_finite g target K)).card ∧
          K < sententialMaxStackHeight (trace.get k) := by
  classical
  let C :=
    (Set.Finite.toFinset
      (targetCompatibleBoundedSurfaceForms_finite g target K)).card
  by_cases hn : n < C
  · exact Or.inl (by simpa [C] using hn)
  · have hC_le_n : C ≤ n := Nat.le_of_not_gt hn
    have hm : trace.length - 1 - C + C < trace.length := by
      omega
    have hhigh :=
      exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := K) (N := C) (n := n) (B := B)
        (by
          intro k hk hlt
          exact hbeforeBound k hk (by simpa [C] using hlt))
        (by simpa [C] using hm)
        (by simpa [C] using hgt)
    exact Or.inr (by simpa [C] using hhigh)

/-- Length-uniform version of
`exists_high_stack_between_late_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound`.
The target-compatible surface cardinal is bounded by the length-bounded surface cardinal, so
the dichotomy can use a constant depending only on the target length bound `L`. -/
theorem exists_high_stack_between_late_lengthBound_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K L n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (target.map ISym.terminal))
    (hminLength : ∀ k,
      g.DerivesIn k [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k)
    (hminBound : ∀ C' : ℕ,
      (∃ trace' : List (List g.ISym),
        IsDerivationTrace g trace' ∧
          trace'.length = n + 1 ∧
          trace'.head? = some [ISym.indexed g.initial []] ∧
          trace'.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          ∀ j (hj : j < trace'.length),
            sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
        B ≤ C')
    (hbeforeBound : ∀ k (hk : k < trace.length),
      k < trace.length - 1 -
          (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hgt :
      K + (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card < B) :
    n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card ∨
      ∃ k : Fin trace.length,
        trace.length - 1 -
            (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card ≤ k.1 ∧
          k.1 ≤
            trace.length - 1 -
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card +
              (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card ∧
          trace.length - 1 - k.1 ≤
            (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card ∧
          K < sententialMaxStackHeight (trace.get k) := by
  classical
  let Ct :=
    (Set.Finite.toFinset
      (targetCompatibleBoundedSurfaceForms_finite g target K)).card
  let CL := (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card
  have hCtCL : Ct ≤ CL := by
    simpa [Ct, CL] using
      targetCompatibleBoundedSurfaceForms_card_le_boundedSurfaceForms_card_lengthBound
        (g := g) (stackBound := K) htargetLen
  by_cases hn : n < CL
  · exact Or.inl (by simpa [CL] using hn)
  · have hCL_le_n : CL ≤ n := Nat.le_of_not_gt hn
    have hm : trace.length - 1 - CL + Ct < trace.length := by
      omega
    obtain ⟨k, hkLower, hkUpper, hsuffixBudget, hhigh⟩ :=
      exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := K) (N := CL) (n := n) (B := B)
        (by
          intro k hk hlt
          exact hbeforeBound k hk (by simpa [CL] using hlt))
        (by simpa [Ct, CL] using hm)
        (by simpa [CL] using hgt)
    refine Or.inr ⟨k, by simpa [CL] using hkLower, ?_, by simpa [CL] using hsuffixBudget,
      hhigh⟩
    have hupper :
        trace.length - 1 - CL + Ct ≤ trace.length - 1 - CL + CL :=
      Nat.add_le_add_left hCtCL (trace.length - 1 - CL)
    exact le_trans (by simpa [Ct, CL] using hkUpper) (by simpa [CL] using hupper)

/-- A positionwise terminal-preserving substack replacement preserves sentential-form length. -/
theorem length_eq_of_forall₂_symbol_substack_bound
    {g : IndexedGrammar T} {K : ℕ} {xs ys : List g.ISym}
    (hrel : List.Forall₂
      (fun s t =>
        match s, t with
        | ISym.terminal a, ISym.terminal b => a = b
        | ISym.indexed A σ, ISym.indexed C τ =>
            A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
        | _, _ => False)
      xs ys) :
    ys.length = xs.length := by
  induction hrel with
  | nil => rfl
  | cons _hhead _htail ih =>
      simp [ih]

/-- A positionwise terminal-preserving substack replacement preserves the visible terminal
yield of a sentential form. -/
theorem sententialTerminals_eq_of_forall₂_symbol_substack_bound
    {g : IndexedGrammar T} {K : ℕ} {xs ys : List g.ISym}
    (hrel : List.Forall₂
      (fun s t =>
        match s, t with
        | ISym.terminal a, ISym.terminal b => a = b
        | ISym.indexed A σ, ISym.indexed C τ =>
            A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
        | _, _ => False)
      xs ys) :
    sententialTerminals ys = sententialTerminals xs := by
  induction hrel with
  | nil =>
      simp
  | cons hhead _htail ih =>
      rename_i s t xs ys
      cases s <;> cases t <;> simp at hhead ⊢
      · simp [hhead, ih]
      · exact ih

/-- A positionwise terminal-preserving substack replacement preserves the number of live
indexed nonterminals. -/
theorem sententialNonterminalCount_eq_of_forall₂_symbol_substack_bound
    {g : IndexedGrammar T} {K : ℕ} {xs ys : List g.ISym}
    (hrel : List.Forall₂
      (fun s t =>
        match s, t with
        | ISym.terminal a, ISym.terminal b => a = b
        | ISym.indexed A σ, ISym.indexed C τ =>
            A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
        | _, _ => False)
      xs ys) :
    sententialNonterminalCount ys = sententialNonterminalCount xs := by
  induction hrel with
  | nil =>
      simp
  | cons hhead _htail ih =>
      rename_i s t xs ys
      cases s <;> cases t <;> simp at hhead ⊢
      · exact ih
      · omega

/-- A target-compatible sentential form remains target-compatible after a positionwise
terminal-preserving substack replacement; the finite representative is the truncated surface
of the replacement. -/
theorem surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms_of_forall₂_symbol_substack_bound
    {g : IndexedGrammar T} {K : ℕ} {target : List T} {xs ys : List g.ISym}
    (hrel : List.Forall₂
      (fun s t =>
        match s, t with
        | ISym.terminal a, ISym.terminal b => a = b
        | ISym.indexed A σ, ISym.indexed C τ =>
            A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
        | _, _ => False)
      xs ys)
    (hlen : xs.length ≤ target.length)
    (hterm : (sententialTerminals xs).Sublist target) :
    surfaceOfTruncatedForm K ys ∈
      targetCompatibleBoundedSurfaceForms g target K := by
  apply surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms
  · rw [length_eq_of_forall₂_symbol_substack_bound hrel]
    exact hlen
  · rw [sententialTerminals_eq_of_forall₂_symbol_substack_bound hrel]
    exact hterm

/-- A positionwise terminal-preserving substack replacement has the advertised stack bound on
the replacement sentential form. -/
theorem sententialMaxStackHeight_le_of_forall₂_symbol_substack_bound
    {g : IndexedGrammar T} {K : ℕ} {xs ys : List g.ISym}
    (hrel : List.Forall₂
      (fun s t =>
        match s, t with
        | ISym.terminal a, ISym.terminal b => a = b
        | ISym.indexed A σ, ISym.indexed C τ =>
            A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
        | _, _ => False)
      xs ys) :
    sententialMaxStackHeight ys ≤ K := by
  induction hrel with
  | nil =>
      simp
  | cons hhead _htail ih =>
      rename_i s t xs ys
      cases s <;> cases t <;> simp at hhead ⊢
      · exact ih
      · exact ⟨hhead.2.2, ih⟩

/-- Whole-form accepting suffix shrinking with the concrete singleton split and local
minimality certificates retained. The shrunken suffix derivation is stack-bounded by the
uniform replacement height plus the summed replacement step budgets. -/
theorem exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ parts : List (ℕ × List T),
            ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
              parts.length = (trace.get ⟨i, hi⟩).length ∧
                (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
                (parts.flatMap fun p => p.2) = target ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  (trace.get ⟨i, hi⟩) parts ∧
                (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
                (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  ys parts' ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                parts'.length = parts.length ∧
                List.Forall₂
                  (fun sp tq =>
                    match sp.1, tq.1 with
                    | ISym.terminal a, ISym.terminal b =>
                        a = b ∧ tq.2 = sp.2
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧
                          tq.2.2 = sp.2.2 ∧
                          tq.2.1 ≤ sp.2.1 ∧
                          τ.Sublist σ ∧
                          τ.length ≤ K ∧
                          g.DerivesIn tq.2.1 [ISym.indexed C τ]
                            (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                          ∀ ρ : List g.flag, ∀ k : ℕ,
                            k ≤ sp.2.1 →
                            g.DerivesIn k [ISym.indexed C ρ]
                              (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                            ρ.Sublist τ → ρ = τ
                    | _, _ => False)
                  ((trace.get ⟨i, hi⟩).zip parts) (ys.zip parts') ∧
                sententialMaxStackHeight ys ≤ K ∧
                StackBoundedDerivesIn g (K + (parts'.map fun p => p.1).sum)
                  ((parts'.map fun p => p.1).sum) ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hysBound : sententialMaxStackHeight ys ≤ K :=
    sententialMaxStackHeight_le_of_forall₂_symbol_substack_bound hrel
  have hbounded :
      StackBoundedDerivesIn g (K + (parts'.map fun p => p.1).sum)
        ((parts'.map fun p => p.1).sum) ys
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
      (g := g) (B := K) hNF hder hysBound
  exact ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hysBound, hbounded⟩

/-- Surface-packaged form of
`exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget_with_minimality`.
It keeps the finite target-compatible surface representative and the local minimality
certificates for each indexed replacement in one result. -/
theorem exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ parts : List (ℕ × List T),
            ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
              parts.length = (trace.get ⟨i, hi⟩).length ∧
                (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
                (parts.flatMap fun p => p.2) = target ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  (trace.get ⟨i, hi⟩) parts ∧
                (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
                (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  ys parts' ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                parts'.length = parts.length ∧
                List.Forall₂
                  (fun sp tq =>
                    match sp.1, tq.1 with
                    | ISym.terminal a, ISym.terminal b =>
                        a = b ∧ tq.2 = sp.2
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧
                          tq.2.2 = sp.2.2 ∧
                          tq.2.1 ≤ sp.2.1 ∧
                          τ.Sublist σ ∧
                          τ.length ≤ K ∧
                          g.DerivesIn tq.2.1 [ISym.indexed C τ]
                            (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                          ∀ ρ : List g.flag, ∀ k : ℕ,
                            k ≤ sp.2.1 →
                            g.DerivesIn k [ISym.indexed C ρ]
                              (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                            ρ.Sublist τ → ρ = τ
                    | _, _ => False)
                  ((trace.get ⟨i, hi⟩).zip parts) (ys.zip parts') ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                surfaceOfTruncatedForm K ys ∈
                  targetCompatibleBoundedSurfaceForms g target K ∧
                StackBoundedDerivesIn g (K + (parts'.map fun p => p.1).sum)
                  ((parts'.map fun p => p.1).sum) ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hysBound, hbounded⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hlenEq :
      ys.length = (trace.get ⟨i, hi⟩).length :=
    length_eq_of_forall₂_symbol_substack_bound hrel
  have htermEq :
      sententialTerminals ys =
        sententialTerminals (trace.get ⟨i, hi⟩) :=
    sententialTerminals_eq_of_forall₂_symbol_substack_bound hrel
  have hntEq :
      sententialNonterminalCount ys =
        sententialNonterminalCount (trace.get ⟨i, hi⟩) :=
    sententialNonterminalCount_eq_of_forall₂_symbol_substack_bound hrel
  have herase :
      eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      hysBound
  have hxlen :
      (trace.get ⟨i, hi⟩).length ≤ target.length :=
    accepting_derivationTrace_get_length_le_target_of_isNormalForm
      hNF htrace hlast hi
  have hxterm : (sententialTerminals (trace.get ⟨i, hi⟩)).Sublist target := by
    have hsuffix :=
      isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
    have hsub := derivesIn_sententialTerminals_sublist (g := g) hsuffix
    simpa using hsub
  have hsurface :
      surfaceOfTruncatedForm K ys ∈
        targetCompatibleBoundedSurfaceForms g target K :=
    surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms_of_forall₂_symbol_substack_bound
      hrel hxlen hxterm
  exact ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hlenEq, htermEq, hntEq, hysBound,
    herase, hsurface, hbounded⟩

/-- Whole-form accepting suffix shrinking plus its bounded-stack suffix derivation. The
replacement sentential form has all visible stacks bounded by `K`, and its derivation to the
target is stack-bounded by `K + n'`. -/
theorem exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ ys : List g.ISym, ∃ n' : ℕ,
              n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                sententialMaxStackHeight ys ≤ K ∧
                StackBoundedDerivesIn g (K + n') n' ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨ys, n', hn', hrel, hder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hysBound : sententialMaxStackHeight ys ≤ K :=
    sententialMaxStackHeight_le_of_forall₂_symbol_substack_bound hrel
  have hbounded :
      StackBoundedDerivesIn g (K + n') n' ys
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
      (g := g) (B := K) hNF hder hysBound
  exact ⟨ys, n', hn', hrel, hysBound, hbounded⟩

/-- Whole-form accepting suffix shrinking packaged with its finite surface representative.
The replacement has the same visible length, terminal yield, and number of live nonterminals
as the trace position it replaces; since its stacks are bounded, its truncated surface erases
back to the replacement itself and belongs to the finite target-compatible surface set. -/
theorem exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ ys : List g.ISym, ∃ n' : ℕ,
              n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                surfaceOfTruncatedForm K ys ∈
                  targetCompatibleBoundedSurfaceForms g target K ∧
                StackBoundedDerivesIn g (K + n') n' ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨ys, n', hn', hrel, hysBound, hbounded⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hlenEq :
      ys.length = (trace.get ⟨i, hi⟩).length :=
    length_eq_of_forall₂_symbol_substack_bound hrel
  have htermEq :
      sententialTerminals ys =
        sententialTerminals (trace.get ⟨i, hi⟩) :=
    sententialTerminals_eq_of_forall₂_symbol_substack_bound hrel
  have hntEq :
      sententialNonterminalCount ys =
        sententialNonterminalCount (trace.get ⟨i, hi⟩) :=
    sententialNonterminalCount_eq_of_forall₂_symbol_substack_bound hrel
  have herase :
      eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys :=
    eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
      hysBound
  have hxlen :
      (trace.get ⟨i, hi⟩).length ≤ target.length :=
    accepting_derivationTrace_get_length_le_target_of_isNormalForm
      hNF htrace hlast hi
  have hxterm : (sententialTerminals (trace.get ⟨i, hi⟩)).Sublist target := by
    have hsuffix :=
      isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
    have hsub := derivesIn_sententialTerminals_sublist (g := g) hsuffix
    simpa using hsub
  have hsurface :
      surfaceOfTruncatedForm K ys ∈
        targetCompatibleBoundedSurfaceForms g target K :=
    surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms_of_forall₂_symbol_substack_bound
      hrel hxlen hxterm
  exact ⟨ys, n', hn', hrel, hlenEq, htermEq, hntEq, hysBound,
    herase, hsurface, hbounded⟩

/-- Finite-surface version of the whole-form minimal-stack bridge. It is enough to prove a
bounded prefix reachability statement for every member of the finite target-compatible
surface set; the whole-form suffix shrinker supplies one such surface, whose erasure is the
replacement sentential form used to splice a shorter bounded accepting derivation. -/
theorem exists_bound_minimal_stackBound_le_of_reachable_targetCompatible_surface_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ Bpre : ℕ,
              trace.length - 1 - i ≤ N →
              (∀ surface : SurfaceForm g K,
                surface ∈ targetCompatibleBoundedSurfaceForms g target K →
                StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
                  (eraseSurfaceForm surface)) →
              ∃ ys : List g.ISym, ∃ n' : ℕ,
                n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                surfaceOfTruncatedForm K ys ∈
                  targetCompatibleBoundedSurfaceForms g target K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []] ys ∧
                StackBoundedDerivesIn g (K + n') n' ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hsuffixBudget hreachable
  obtain ⟨ys, n', hn', hrel, hlenEq, htermEq, hntEq, _hysBound,
    herase, hsurface, hboundedSuffix⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hpreSurface :
      StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
        (eraseSurfaceForm (surfaceOfTruncatedForm K ys)) :=
    hreachable (surfaceOfTruncatedForm K ys) hsurface
  have hpre :
      StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []] ys := by
    simpa [herase] using hpreSurface
  have hsuffixDerives :
      g.DerivesIn n' ys
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    StackBoundedDerivesIn.to_derivesIn hboundedSuffix
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_reachable_trace_suffix_derivesIn
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (q := n')
      (w := target) (trace := trace) (i := i) (mid := ys)
      hlen hi hminLength hminBound hpre hsuffixDerives hn'
  exact ⟨ys, n', hn', hrel, hlenEq, htermEq, hntEq, hsurface,
    herase, hpre, hboundedSuffix, hB⟩

/-- Stack-bound-only consequence of the finite-surface replacement bridge. If every finite
target-compatible surface is reachable by a prefix staying within `Bpre`, then the stack bound
minimal among shortest accepting traces is controlled by the larger of that prefix bound and
the uniform replacement-suffix bound `K + N`. -/
theorem exists_bound_minimal_stackBound_le_max_of_reachable_targetCompatible_surface_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, i < trace.length →
            ∀ Bpre : ℕ,
              trace.length - 1 - i ≤ N →
              (∀ surface : SurfaceForm g K,
                surface ∈ targetCompatibleBoundedSurfaceForms g target K →
                StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
                  (eraseSurfaceForm surface)) →
              B ≤ max Bpre (K + N) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_reachable_targetCompatible_surface_suffix_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hsuffixBudget hreachable
  obtain ⟨ys, n', hn', _hrel, _hlenEq, _htermEq, _hntEq, _hsurface,
    _herase, hpre, hboundedSuffix, _hBadd⟩ :=
    hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
      i hi Bpre hsuffixBudget hreachable
  have hsteps : i + n' ≤ n := by
    omega
  have hBmax :
      B ≤ max Bpre (K + n') :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_suffix
      (g := g) (n := n) (B := B) (Bpre := Bpre) (Bsuf := K + n')
      (p := i) (q := n') (w := target) (mid := ys)
      hminLength hminBound hpre hboundedSuffix hsteps
  have hmono : max Bpre (K + n') ≤ max Bpre (K + N) := by
    refine Nat.max_le.mpr ⟨Nat.le_max_left _ _, ?_⟩
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact le_trans hBmax hmono

/-- Finite-surface replacement bridge with a shortened prefix.

The earlier reachable-surface bridge requires the replacement middle form to be reachable in
exactly the original trace-prefix length `i`. For the finite-frontier argument we need the
stronger usable form: if the replacement surface is reachable by any bounded prefix of length
at most `i`, then splicing that shorter prefix with the bounded replacement suffix still gives
an accepting derivation no longer than the chosen shortest trace. Hence the minimal stack
bound is controlled by the maximum of the prefix bound and the uniform suffix bound. -/
theorem exists_bound_minimal_stackBound_le_max_of_shorter_reachable_targetCompatible_surface_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, i < trace.length →
            ∀ Bpre : ℕ,
              trace.length - 1 - i ≤ N →
              (∀ surface : SurfaceForm g K,
                surface ∈ targetCompatibleBoundedSurfaceForms g target K →
                ∃ p : ℕ,
                  p ≤ i ∧
                    StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                      (eraseSurfaceForm surface)) →
              B ≤ max Bpre (K + N) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hsuffixBudget hreachable
  obtain ⟨ys, n', hn', _hrel, _hlenEq, _htermEq, _hntEq, _hysBound,
    herase, hsurface, hboundedSuffix⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨p, hp, hpreSurface⟩ :=
    hreachable (surfaceOfTruncatedForm K ys) hsurface
  have hpre :
      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []] ys := by
    simpa [herase] using hpreSurface
  have hsteps : p + n' ≤ n := by
    omega
  have hBmax :
      B ≤ max Bpre (K + n') :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_suffix
      (g := g) (n := n) (B := B) (Bpre := Bpre) (Bsuf := K + n')
      (p := p) (q := n') (w := target) (mid := ys)
      hminLength hminBound hpre hboundedSuffix hsteps
  have hmono : max Bpre (K + n') ≤ max Bpre (K + N) := by
    refine Nat.max_le.mpr ⟨Nat.le_max_left _ _, ?_⟩
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact le_trans hBmax hmono

/-- Whole-form version of the global minimal-stack bridge. If the accepting-trace suffix
shrinker replaces every indexed stack in the displayed sentential form, and that entire
replacement form is reachable by a bounded prefix, then the least stack bound of the chosen
shortest accepting trace is bounded by the prefix bound plus the replacement suffix length. -/
theorem exists_bound_minimal_stackBound_le_of_reachable_symbols_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ Bpre : ℕ,
              trace.length - 1 - i ≤ N →
              (∀ ys : List g.ISym,
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys →
                StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []] ys) →
              ∃ ys : List g.ISym, ∃ n' : ℕ,
                n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                g.DerivesIn n' ys
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_symbols_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hsuffixBudget hreachable
  obtain ⟨ys, n', hn', hrel, hder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hpre :
      StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []] ys :=
    hreachable ys hrel
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_reachable_trace_suffix_derivesIn
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (q := n')
      (w := target) (trace := trace) (i := i)
      hlen hi hminLength hminBound hpre hder hn'
  exact ⟨ys, n', hn', hrel, hder, hB⟩

/-- If the trace-local suffix shrinker produces a modified middle sentential form that is
reachable by a bounded prefix, then the least stack bound of the chosen shortest accepting
trace is bounded by that prefix bound plus the replacement suffix length. This is the exact
global bridge needed by the remaining ancestry/reachability argument. -/
theorem exists_bound_minimal_stackBound_le_of_reachable_indexed_context_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              ∀ u v : List g.ISym, ∀ Bpre : ℕ,
                pref.length ≤ N →
                pref.length + (trace.length - 1 - i) ≤ N →
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                (∀ τ : List g.flag,
                  τ.Sublist σ →
                  τ.length ≤ K →
                  StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
                    (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
                ∃ q m : ℕ, ∃ τ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                  w.Sublist target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ.Sublist σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) ∧
                  B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi A pref σ u v Bpre hpref hbudget hctx hreachable
  obtain ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hpref hbudget u v hctx
  have hpre :
      StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
        (u ++ [ISym.indexed A (pref ++ τ)] ++ v) :=
    hreachable τ hτsub hτlen
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_reachable_trace_suffix_derivesIn
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (q := n')
      (w := target) (trace := trace) (i := i)
      hlen hi hminLength hminBound hpre hreplacement hn'
  exact ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
    hτder, hreplacement, hτmin, hB⟩

/-- Local indexed-context replacement bridge with a shortened prefix.

This is the local counterpart of
`exists_bound_minimal_stackBound_le_max_of_shorter_reachable_targetCompatible_surface_suffix_replacement_budget`.
The context shrinker supplies a replacement stack for one displayed indexed occurrence. If
that replacement context is reachable by any bounded prefix no longer than the original trace
prefix, then it can be spliced with the replacement suffix without increasing the shortest
accepting length. -/
theorem exists_bound_minimal_stackBound_le_of_shorter_reachable_indexed_context_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ pref σ : List g.flag,
              ∀ u v : List g.ISym, ∀ Bpre : ℕ,
                pref.length ≤ N →
                pref.length + (trace.length - 1 - i) ≤ N →
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                (∀ τ : List g.flag,
                  τ.Sublist σ →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
                ∃ q m : ℕ, ∃ τ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                  w.Sublist target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ.Sublist σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) ∧
                  B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi A pref σ u v Bpre hpref hbudget hctx hreachable
  obtain ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hpref hbudget u v hctx
  obtain ⟨p, hp, hpre⟩ := hreachable τ hτsub hτlen
  have hsteps : p + n' ≤ n := by
    omega
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
      (w := target) (mid := u ++ [ISym.indexed A (pref ++ τ)] ++ v)
      hminLength hminBound hpre hreplacement hsteps
  exact ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
    hτder, hreplacement, hτmin, hB⟩

/-- Max-stack form of
`exists_bound_minimal_stackBound_le_of_reachable_indexed_context_suffix_replacement_budget`.
The distinguished symbol is chosen to attain the current sentential maximum stack height; the
only external obligation is reachability of the shrunk middle form. -/
theorem exists_bound_minimal_stackBound_le_of_reachable_max_stack_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ Bpre : ℕ,
              P ≤ Q →
              P + (trace.length - 1 - i) ≤ Q →
              0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              (∀ A : g.nt, ∀ η pref σ τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η = pref ++ σ →
                  pref.length ≤ P →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                  τ.Sublist σ →
                  τ.length ≤ K →
                  StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
                    (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
              ∃ A : g.nt, ∃ η pref σ τ : List g.flag,
                ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                  η = pref ++ σ ∧
                  pref.length ≤ P ∧
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                  w.Sublist target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ.Sublist σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) ∧
                  B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_max_stack_suffix_shrink_replacement_budget
      (g := g) hNF P Q L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hPQ hbudget hpos hreachable
  obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n',
      hmem, hη, hpref, hηmax, hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi hPQ hbudget hpos
  have hpre :
      StackBoundedDerivesIn g Bpre i [ISym.indexed g.initial []]
        (u ++ [ISym.indexed A (pref ++ τ)] ++ v) :=
    hreachable A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_reachable_trace_suffix_derivesIn
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (q := n')
      (w := target) (trace := trace) (i := i)
      hlen hi hminLength hminBound hpre hreplacement hn'
  exact ⟨A, η, pref, σ, τ, u, v, q, m, w, n', hmem, hη, hpref, hηmax, hctx,
    hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin,
    hB⟩

/-- Max-stack replacement bridge with a shortened prefix.

This is the form needed for a pumping argument on the least stack bound: the selected
occurrence has maximum stack height in the current trace position, but the shrunken context
only has to be reachable by some bounded prefix no longer than the original prefix. -/
theorem exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ Bpre : ℕ,
              P ≤ Q →
              P + (trace.length - 1 - i) ≤ Q →
              0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              (∀ A : g.nt, ∀ η pref σ τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η = pref ++ σ →
                  pref.length ≤ P →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                  τ.Sublist σ →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
              ∃ A : g.nt, ∃ η pref σ τ : List g.flag,
                ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                  η = pref ++ σ ∧
                  pref.length ≤ P ∧
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                  w.Sublist target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ.Sublist σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) ∧
                  B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_max_stack_suffix_shrink_replacement_budget
      (g := g) hNF P Q L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hPQ hbudget hpos hreachable
  obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n',
      hmem, hη, hpref, hηmax, hctx, hwt, hwlen, hq, hm, hmSuffix, hn',
      hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi hPQ hbudget hpos
  obtain ⟨p, hp, hpre⟩ :=
    hreachable A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen
  have hsteps : p + n' ≤ n := by
    omega
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
      (w := target) (mid := u ++ [ISym.indexed A (pref ++ τ)] ++ v)
      hminLength hminBound hpre hreplacement hsteps
  exact ⟨A, η, pref, σ, τ, u, v, q, m, w, n', hmem, hη, hpref, hηmax, hctx,
    hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin,
    hB⟩

/-- Canonical max-stack replacement bridge with a shortened prefix.

This is the same minimal-stack bridge as
`exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_suffix_replacement_budget`,
but the external reachability obligation is stated only for the canonical split
`η.take P ++ η.drop P` of the selected maximum stack. This is the form that can be connected
to finite-surface repetitions. -/
theorem
    exists_bound_minimal_stackBound_le_of_shorter_reachable_canonical_max_stack_suffix_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ Bpre : ℕ,
              P ≤ Q →
              P + (trace.length - 1 - i) ≤ Q →
              0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              (∀ A : g.nt, ∀ η τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
              ∃ A : g.nt, ∃ η pref σ τ : List g.flag,
                ∃ u v : List g.ISym, ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                  η = pref ++ σ ∧
                  pref = η.take P ∧
                  σ = η.drop P ∧
                  pref.length ≤ P ∧
                  (P < η.length → pref.length = P) ∧
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v ∧
                  w.Sublist target ∧ w.length ≤ L ∧
                  q ≤ trace.length - 1 - i ∧
                  m ≤ q ∧
                  m ≤ trace.length - 1 - i ∧
                  n' ≤ trace.length - 1 - i ∧
                  τ.Sublist σ ∧ τ.length ≤ K ∧
                  g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                  g.DerivesIn n' (u ++ [ISym.indexed A (pref ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) ∧
                  B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_canonical_max_stack_suffix_shrink_replacement_budget
      (g := g) hNF P Q L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hPQ hbudget hpos hreachable
  obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n',
      hmem, hη, hprefEq, hσEq, hpref, hprefLen, hηmax, hctx, hwt, hwlen, hq, hm,
      hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi hPQ hbudget hpos
  have hctxη :
      trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v := by
    simpa [hη] using hctx
  obtain ⟨p, hp, hpre⟩ :=
    hreachable A η τ u v hmem hηmax hctxη
      (by simpa [hσEq] using hτsub) hτlen
  have hreplacementη :
      g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [hprefEq] using hreplacement
  have hsteps : p + n' ≤ n := by
    omega
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
      (w := target) (mid := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
      hminLength hminBound hpre hreplacementη hsteps
  exact ⟨A, η, pref, σ, τ, u, v, q, m, w, n', hmem, hη, hprefEq, hσEq,
    hpref, hprefLen, hηmax, hctx, hwt, hwlen, hq, hm, hmSuffix, hn', hτsub,
    hτlen, hτder, hreplacement, hτmin, hB⟩

/-- Late-window max-stack replacement bridge. If the prefix before the late window is
`P`-bounded but the least accepting stack bound is larger than `P + N`, the late-window
surface argument supplies a high-stack position with suffix budget at most `N`. The max-stack
shrinker then bounds the least accepting stack bound by the supplied reachable-prefix bound
plus `N`. The remaining, explicitly exposed premise is the real reachability obligation for
the shrunken distinguished max-stack context. -/
theorem exists_bound_minimal_stackBound_le_of_late_window_shorter_reachable_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 - N →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card <
              trace.length →
            P + N < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - N ≤ i →
              i ≤ trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η pref σ τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η = pref ++ σ →
                  pref.length ≤ P →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                  τ.Sublist σ →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
            B ≤ Bpre + N := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_suffix_replacement_budget
      (g := g) hNF P (P + N) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hm hgt hreachable
  obtain ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩ :=
    exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
      (g := g) hNF htrace hlen hhead hlast hminLength hminBound
      (K := P) (N := N) (n := n) (B := B) hbeforeBound hm hgt
  have hP_le : P ≤ P + N := Nat.le_add_right P N
  have hbudget : P + (trace.length - 1 - i.1) ≤ P + N :=
    Nat.add_le_add_left hsuffixBudget P
  have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
    lt_of_le_of_lt (Nat.zero_le P) hhigh
  obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n', _hmem, _hη, _hpref,
      _hηmax, _hctx, _hwt, _hwlen, _hq, _hm, _hmSuffix, hn', _hτsub,
      _hτlen, _hτder, _hreplacement, _hτmin, hB⟩ :=
    hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
      i.1 i.2 Bpre hP_le hbudget hpos
      (by
        intro A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen
        exact hreachable i.1 i.2 hiLower hiUpper hhigh A η pref σ τ u v
          hmem hη hpref hηmax hctx hτsub hτlen)
  have hnN : n' ≤ N := le_trans hn' hsuffixBudget
  omega

/-- Length-uniform cardinal-budget form of the late-window max-stack replacement bridge.
For `C = |boundedSurfaceForms g L P|`, either the chosen shortest accepting derivation already
has fewer than `C` steps, or the late high-stack/max-stack replacement argument bounds the
least accepting stack bound by `Bpre + C`. The only non-arithmetic premise left exposed is
the actual bounded-prefix reachability of the shrunken distinguished max-stack contexts in
the finite late window. -/
theorem exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_shorter_reachable_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
              i ≤ trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η pref σ τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η = pref ++ σ →
                  pref.length ≤ P →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                  τ.Sublist σ →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
            n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ∨
              B ≤ Bpre +
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card := by
  classical
  let C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_suffix_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound
      (g := g) hNF (K := P) (L := L) (n := n) (B := B)
      htargetLen htrace hlen hhead hlast hminLength hminBound
      (by
        intro k hk hlt
        exact hbeforeBound k hk (by simpa [C] using hlt))
      (by simpa [C] using hgt)
  rcases hdich with hn | ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩
  · exact Or.inl (by simpa [C] using hn)
  · have hP_le : P ≤ P + C := Nat.le_add_right P C
    have hbudget : P + (trace.length - 1 - i.1) ≤ P + C :=
      Nat.add_le_add_left (by simpa [C] using hsuffixBudget) P
    have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
      lt_of_le_of_lt (Nat.zero_le P) hhigh
    obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n', _hmem, _hη, _hpref,
        _hηmax, _hctx, _hwt, _hwlen, _hq, _hm, _hmSuffix, hn', _hτsub,
        _hτlen, _hτder, _hreplacement, _hτmin, hB⟩ :=
      hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
        i.1 i.2 Bpre hP_le hbudget hpos
        (by
          intro A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen
          exact hreachable i.1 i.2
            (by simpa [C] using hiLower) (by simpa [C] using hiUpper) hhigh
            A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen)
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

/-- Canonical-split version of
`exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_shorter_reachable_max_stack`.
The remaining reachability premise is restricted to the selected maximum stack split as
`η.take P ++ η.drop P`, which is the split exposed by finite `P`-surfaces. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_shorter_reachable_canonical_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
              i ≤ trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
            n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ∨
              B ≤ Bpre +
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card := by
  classical
  let C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_canonical_max_stack_suffix_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound
      (g := g) hNF (K := P) (L := L) (n := n) (B := B)
      htargetLen htrace hlen hhead hlast hminLength hminBound
      (by
        intro k hk hlt
        exact hbeforeBound k hk (by simpa [C] using hlt))
      (by simpa [C] using hgt)
  rcases hdich with hn | ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩
  · exact Or.inl (by simpa [C] using hn)
  · have hP_le : P ≤ P + C := Nat.le_add_right P C
    have hbudget : P + (trace.length - 1 - i.1) ≤ P + C :=
      Nat.add_le_add_left (by simpa [C] using hsuffixBudget) P
    have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
      lt_of_le_of_lt (Nat.zero_le P) hhigh
    obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n', _hmem, _hη, _hprefEq,
        _hσEq, _hpref, _hprefLen, _hηmax, _hctx, _hwt, _hwlen, _hq, _hm,
        _hmSuffix, hn', _hτsub, _hτlen, _hτder, _hreplacement, _hτmin, hB⟩ :=
      hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
        i.1 i.2 Bpre hP_le hbudget hpos
        (by
          intro A η τ u v hmem hηmax hctx hτsub hτlen
          exact hreachable i.1 i.2
            (by simpa [C] using hiLower) (by simpa [C] using hiUpper) hhigh
            A η τ u v hmem hηmax hctx hτsub hτlen)
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

/-- Certified canonical late-window replacement bridge.

This variant passes the actual suffix-shrinker certificate for the chosen `τ` to the
remaining reachability premise. The premise therefore only has to prove prefix reachability
for replacements that already preserve the relevant local future derivation. -/
theorem exists_bound_minimal_stackBound_le_of_late_window_shorter_reachable_certified_canonical_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 - N →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card <
              trace.length →
            P + N < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - N ≤ i →
              i ≤ trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ : List g.flag,
                ∀ u v : List g.ISym, ∀ q m : ℕ, ∀ w : List T, ∀ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  w.Sublist target →
                  w.length ≤ L →
                  q ≤ trace.length - 1 - i →
                  m ≤ q →
                  m ≤ trace.length - 1 - i →
                  n' ≤ trace.length - 1 - i →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
            B ≤ Bpre + N := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_canonical_max_stack_suffix_shrink_replacement_budget
      (g := g) hNF P (P + N) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hm hgt hreachable
  obtain ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩ :=
    exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
      (g := g) hNF htrace hlen hhead hlast hminLength hminBound
      (K := P) (N := N) (n := n) (B := B) hbeforeBound hm hgt
  have hP_le : P ≤ P + N := Nat.le_add_right P N
  have hbudget : P + (trace.length - 1 - i.1) ≤ P + N :=
    Nat.add_le_add_left hsuffixBudget P
  have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
    lt_of_le_of_lt (Nat.zero_le P) hhigh
  obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n',
      hmem, hη, hprefEq, hσEq, _hpref, _hprefLen, hηmax, hctx, hwt, hwlen,
      hq, hm, hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget hpos
  have hctxη :
      trace.get i = u ++ [ISym.indexed A η] ++ v := by
    simpa [hη] using hctx
  have hτsubDrop : τ.Sublist (η.drop P) := by
    simpa [hσEq] using hτsub
  have hτderη :
      g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [hprefEq] using hτder
  have hreplacementη :
      g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [hprefEq] using hreplacement
  have hτminη :
      ∀ ρ : List g.flag, ∀ k : ℕ,
        k ≤ q →
        g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ.Sublist τ → ρ = τ := by
    intro ρ k hk hρder hρsub
    exact hτmin ρ k hk (by simpa [hprefEq] using hρder) hρsub
  obtain ⟨p, hp, hpre⟩ :=
    hreachable i.1 i.2 hiLower hiUpper hhigh A η τ u v q m w n'
      hmem hηmax hctxη hwt hwlen hq hm hmSuffix hn' hτsubDrop hτlen
      hτderη hreplacementη hτminη
  have hsteps : p + n' ≤ n := by
    omega
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
      (w := target) (mid := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
      hminLength hminBound hpre hreplacementη hsteps
  have hnN : n' ≤ N := le_trans hn' hsuffixBudget
  omega

/-- Certificate-facing form of the certified canonical late-window bridge.

The local shrinker already supplies a counted derivation from the replaced singleton stack to
the selected subword. This wrapper converts that counted derivation to an `NFYield` certificate
before invoking the remaining prefix-reachability premise, so later ancestry arguments can use
the parse-tree first-step infrastructure directly. -/
theorem exists_bound_minimal_stackBound_le_of_late_window_certificate_reachable_canonical_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 - N →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card <
              trace.length →
            P + N < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - N ≤ i →
              i ≤ trace.length - 1 - N +
                (Set.Finite.toFinset
                  (targetCompatibleBoundedSurfaceForms_finite g target P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ : List g.flag,
                ∀ u v : List g.ISym, ∀ q m : ℕ, ∀ w : List T, ∀ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  w.Sublist target →
                  w.length ≤ L →
                  q ≤ trace.length - 1 - i →
                  m ≤ q →
                  m ≤ trace.length - 1 - i →
                  n' ≤ trace.length - 1 - i →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A (η.take P ++ τ) w →
                  g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
            B ≤ Bpre + N := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_late_window_shorter_reachable_certified_canonical_max_stack
      (g := g) hNF P N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hm hgt hreachable
  exact hK target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hm hgt
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hreplacement hτmin
      have hcert : NFYield g A (η.take P ++ τ) w :=
        NFYield.of_derivesIn_isNormalForm (g := g) hNF hτder
      exact hreachable i hi hlow hup hhigh A η τ u v q m w n'
        hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
        hτder hcert hreplacement hτmin)

/-- Certified canonical late-window dichotomy.

This is the `n < C ∨ B ≤ Bpre + C` form needed by the generated-word wrapper, but its
reachability premise is restricted to the concrete suffix `τ` produced by the canonical
shrinker and receives the corresponding singleton parse certificate. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_canonical_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n B : ℕ, ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.length = n + 1 →
          trace.head? = some [ISym.indexed g.initial []] →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ k,
            g.DerivesIn k [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ k) →
          (∀ C' : ℕ,
            (∃ trace' : List (List g.ISym),
              IsDerivationTrace g trace' ∧
                trace'.length = n + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ j (hj : j < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
              B ≤ C') →
          ∀ Bpre : ℕ,
            (∀ k (hk : k < trace.length),
              k < trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 -
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
              i ≤ trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                  (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ : List g.flag,
                ∀ u v : List g.ISym, ∀ q m : ℕ, ∀ w : List T, ∀ n' : ℕ,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  w.Sublist target →
                  w.length ≤ L →
                  q ≤ trace.length - 1 - i →
                  m ≤ q →
                  m ≤ trace.length - 1 - i →
                  n' ≤ trace.length - 1 - i →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A (η.take P ++ τ) w →
                  g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
            n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ∨
              B ≤ Bpre +
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card := by
  classical
  let C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_canonical_max_stack_suffix_shrink_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound
      (g := g) hNF (K := P) (L := L) (n := n) (B := B)
      htargetLen htrace hlen hhead hlast hminLength hminBound
      (by
        intro k hk hlt
        exact hbeforeBound k hk (by simpa [C] using hlt))
      (by simpa [C] using hgt)
  rcases hdich with hn | ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩
  · exact Or.inl (by simpa [C] using hn)
  · have hP_le : P ≤ P + C := Nat.le_add_right P C
    have hbudget : P + (trace.length - 1 - i.1) ≤ P + C :=
      Nat.add_le_add_left (by simpa [C] using hsuffixBudget) P
    have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
      lt_of_le_of_lt (Nat.zero_le P) hhigh
    obtain ⟨A, η, pref, σ, τ, u, v, q, m, w, n',
        hmem, hη, hprefEq, hσEq, _hpref, _hprefLen, hηmax, hctx, hwt, hwlen,
        hq, hm, hmSuffix, hn', hτsub, hτlen, hτder, hreplacement, hτmin⟩ :=
      hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget hpos
    have hctxη :
        trace.get i = u ++ [ISym.indexed A η] ++ v := by
      simpa [hη] using hctx
    have hτsubDrop : τ.Sublist (η.drop P) := by
      simpa [hσEq] using hτsub
    have hτderη :
        g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [hprefEq] using hτder
    have hcertη : NFYield g A (η.take P ++ τ) w :=
      NFYield.of_derivesIn_isNormalForm (g := g) hNF hτderη
    have hreplacementη :
        g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
          (target.map fun a => (ISym.terminal a : g.ISym)) := by
      simpa [hprefEq] using hreplacement
    have hτminη :
        ∀ ρ : List g.flag, ∀ k : ℕ,
          k ≤ q →
          g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          ρ.Sublist τ → ρ = τ := by
      intro ρ k hk hρder hρsub
      exact hτmin ρ k hk (by simpa [hprefEq] using hρder) hρsub
    obtain ⟨p, hp, hpre⟩ :=
      hreachable i.1 i.2
        (by simpa [C] using hiLower)
        (by simpa [C] using hiUpper)
        hhigh A η τ u v q m w n' hmem hηmax hctxη hwt hwlen hq hm
        hmSuffix hn' hτsubDrop hτlen hτderη hcertη hreplacementη hτminη
    have hsteps : p + n' ≤ n := by
      omega
    have hB :
        B ≤ Bpre + n' :=
      minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
        (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
        (w := target) (mid := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
        hminLength hminBound hpre hreplacementη hsteps
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

theorem stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_stack
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hσ : σ.length ≤ K)
    (h : g.DerivesIn n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (K + n) n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  apply stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
    (g := g) hNF h
  simpa using hσ

theorem stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {N K n : ℕ} {A : g.nt} {pref σ : List g.flag} {w : List T}
    (hpref : pref.length ≤ N)
    (hσ : σ.length ≤ K)
    (h : g.DerivesIn n [ISym.indexed A (pref ++ σ)]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    StackBoundedDerivesIn g (N + K + n) n [ISym.indexed A (pref ++ σ)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hstart : sententialMaxStackHeight ([ISym.indexed A (pref ++ σ)] : List g.ISym) ≤
      N + K := by
    simp [List.length_append]
    omega
  have hbounded :=
    stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
      (g := g) (B := N + K) hNF h hstart
  simpa [Nat.add_assoc] using hbounded

/-- Local shrinking plus normal-form stack growth yields a uniformly stack-bounded derivation.
For a fixed combined budget `N`, the bound is independent of the original visible suffix `σ`:
first shrink to a locally budget-minimal sub-suffix of bounded length, then use the normal-form
`initial stack + steps` bound. -/
theorem exists_stackBoundedDerivesIn_of_derivesIn_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w.Sublist target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          pref.length + n ≤ N →
          ∃ m : ℕ, ∃ τ : List g.flag,
            m ≤ n ∧ τ.Sublist σ ∧ τ.length ≤ K ∧
            StackBoundedDerivesIn g (N + K + N) m
              [ISym.indexed A (pref ++ τ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_generating_prefixed_suffix_for_bounded_prefix_budget
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτder, hτsub, hτlen, _hτmin⟩ :=
    hK pref hpref n A σ w hwt hder hbudget
  have hbounded :
      StackBoundedDerivesIn g (N + K + m) m
        [ISym.indexed A (pref ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
      (g := g) hNF hpref hτlen hτder
  refine ⟨m, τ, hm_le, hτsub, hτlen, ?_⟩
  exact StackBoundedDerivesIn.mono_bound (by omega) hbounded

/-- Length-uniform version of
`exists_stackBoundedDerivesIn_of_derivesIn_bounded_prefix_budget`. For every target of length
at most `L`, one stack bound works for all derivations whose live-prefix/step budget is at
most `N`. -/
theorem exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            pref.length + n ≤ N →
            ∃ m : ℕ, ∃ τ : List g.flag,
              m ≤ n ∧ τ.Sublist σ ∧ τ.length ≤ K ∧
              StackBoundedDerivesIn g (N + K + N) m
                [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_locally_budgeted_generating_prefixed_suffix_for_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτder, hτsub, hτlen, _hτmin⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder hbudget
  have hbounded :
      StackBoundedDerivesIn g (N + K + m) m
        [ISym.indexed A (pref ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
      (g := g) hNF hpref hτlen hτder
  refine ⟨m, τ, hm_le, hτsub, hτlen, ?_⟩
  exact StackBoundedDerivesIn.mono_bound (by omega) hbounded

/-- Certificate-side form of
`exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget`.
Under a fixed live-prefix/step budget, the shrunken derivation has a parse certificate whose
stack bound is uniform in the original derivation. -/
theorem exists_stackBounded_certificate_of_derivesIn_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            pref.length + n ≤ N →
            ∃ m : ℕ, ∃ τ : List g.flag,
              m ≤ n ∧ τ.Sublist σ ∧ τ.length ≤ K ∧
              NFYield.StackBounded g (N + K + N + N) A (pref ++ τ) w := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτsub, hτlen, hbounded⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder hbudget
  have hcert0 :
      NFYield.StackBounded g ((N + K + N) + m) A (pref ++ τ) w :=
    NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm
      (g := g) hNF hbounded
  have hcert :
      NFYield.StackBounded g (N + K + N + N) A (pref ++ τ) w :=
    NFYield.StackBounded.mono_bound (by omega) hcert0
  exact ⟨m, τ, hm_le, hτsub, hτlen, hcert⟩

/-- Initial-stack specialization of
`exists_stackBounded_certificate_of_derivesIn_target_length_bounded_prefix_budget`. -/
theorem exists_bound_initial_stackBounded_certificate_of_derivesIn_target_length_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n : ℕ,
          g.DerivesIn n [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) →
          n ≤ N →
          NFYield.StackBounded g (N + K + N + N) g.initial [] target := by
  obtain ⟨K, hK⟩ :=
    exists_stackBounded_certificate_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n hder hn
  obtain ⟨m, τ, _hm_le, hτsub, _hτlen, hcert⟩ :=
    hK target htargetLen ([] : List g.flag) (by simp) n g.initial []
      target (List.Sublist.refl target) hder (by simpa using hn)
  have hτnil : τ = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen : τ.length ≤ 0 := by
      simpa using hτsub.length_le
    omega
  simpa [hτnil] using hcert

/-- If the visible suffix is globally sublist-minimal for its prefixed nonterminal/yield, the
length-uniform forced-pop bound controls the original stack directly. Combined with normal-form
stack growth, this gives a bounded-stack derivation without replacing the suffix. -/
theorem exists_stackBoundedDerivesIn_of_global_minimal_derivesIn_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ.Sublist σ → τ = σ) →
            pref.length + n ≤ N →
            StackBoundedDerivesIn g (N + (K + N) + N) n
              [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_minimal_suffix_length_of_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin hbudget
  have hσlen : σ.length ≤ K + N :=
    hK target htargetLen pref hpref n A σ w hwt hder hmin hbudget
  have hbounded :
      StackBoundedDerivesIn g (N + (K + N) + n) n
        [ISym.indexed A (pref ++ σ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
      (g := g) hNF (N := N) (K := K + N) hpref hσlen hder
  exact StackBoundedDerivesIn.mono_bound (by omega) hbounded

/-- Unbudgeted counterpart of
`exists_stackBoundedDerivesIn_of_global_minimal_derivesIn_target_length_bounded_prefix_budget`.
If the visible suffix is globally sublist-minimal for its prefixed nonterminal/yield, its
length is bounded uniformly over all targets of length at most `L`; normal-form stack growth
then gives a stack-bounded derivation with bound depending only on that initial bound and the
actual derivation length. -/
theorem exists_stackBoundedDerivesIn_of_global_minimal_derivesIn_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ.Sublist σ → τ = σ) →
            StackBoundedDerivesIn g (N + K + n) n
              [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_minimal_generating_prefixed_suffix_length_for_target_length_bounded_prefix
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin
  have hσlen : σ.length ≤ K :=
    hK target htargetLen pref hpref n A σ w hwt hder hmin
  exact
    stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
      (g := g) hNF (N := N) (K := K) hpref hσlen hder

/-- Length-uniform unbudgeted shrinking-to-bounded-stack bridge. This removes the dependence
on a fixed target word and original suffix length, but the stack bound still contains the
count `m` of the shrunken derivation. Removing that remaining count dependency is the global
shortest-derivation/stack-control problem. -/
theorem exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ m : ℕ, ∃ τ : List g.flag,
              τ.Sublist σ ∧ τ.length ≤ K ∧
              StackBoundedDerivesIn g (N + K + m) m
                [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ.Sublist τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_counted_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder
  obtain ⟨m, τ, hτsub, hτlen, hτder, hτmin⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder
  have hbounded :
      StackBoundedDerivesIn g (N + K + m) m
        [ISym.indexed A (pref ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_singleton_to_terminals_of_derivesIn_isNormalForm_bounded_prefix_stack
      (g := g) hNF hpref hτlen hτder
  exact ⟨m, τ, hτsub, hτlen, hbounded, hτmin⟩

/-- If a shortest accepting derivation has step count at most `N` and the target has length at
most `L`, then every stack in its trace is already bounded by `N`. Consequently the shortest
derivation has fewer steps than the finite surface space with stack bound `N`. -/
theorem exists_bounded_accepting_trace_and_surface_bound_of_minimal_derivesIn_steps_le
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {N L : ℕ} :
    ∀ target : List T,
      target.length ≤ L →
      ∀ n : ℕ,
        g.DerivesIn n [ISym.indexed g.initial []]
          (target.map fun a => (ISym.terminal a : g.ISym)) →
        (∀ m,
          g.DerivesIn m [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
        n ≤ N →
        ∃ trace : List (List g.ISym),
          IsDerivationTrace g trace ∧
          trace.length = n + 1 ∧
          trace.head? = some [ISym.indexed g.initial []] ∧
          trace.getLast? =
            some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
          (∀ i (hi : i < trace.length),
            sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N) ∧
          n < (Set.Finite.toFinset
            (boundedSurfaceForms_finite g L N)).card := by
  intro target htargetLen n hder hmin hnN
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  have hstack :
      ∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N := by
    intro i hi
    have hi_le_n : i ≤ n := by omega
    exact le_trans
      (accepting_derivationTrace_get_maxStackHeight_le_index_of_isNormalForm
        hNF htrace hhead hi)
      (le_trans hi_le_n hnN)
  have hcard :=
    minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound_lengthBound
      (B := N) hNF htrace hlen hhead hlast hmin htargetLen hstack
  refine ⟨trace, htrace, hlen, hhead, hlast, hstack, ?_⟩
  omega

/-- Length-uniform finite-search bound obtained from the current budgeted shrinking bridge.

If a shortest accepting derivation has step count at most `N` and the target has length at
most `L`, the local shrinking infrastructure produces an accepting trace with all stacks
bounded by `N + K + N`; the trace therefore has fewer than the corresponding finite
bounded-surface configurations. The remaining global inclusion work is to remove the
hypothesis `n ≤ N` by proving an input-length bound on shortest accepting derivations/stacks. -/
theorem exists_bound_bounded_accepting_trace_and_surface_bound_of_minimal_derivesIn_target_length_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n : ℕ,
          g.DerivesIn n [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ m,
            g.DerivesIn m [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
          n ≤ N →
          ∃ trace : List (List g.ISym),
            IsDerivationTrace g trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? =
              some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N) ∧
            n < (Set.Finite.toFinset
              (boundedSurfaceForms_finite g L (N + K + N))).card := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n hder hmin hnN
  obtain ⟨m, τ, hm_le, hτsub, _hτlen, hbounded0⟩ :=
    hK target htargetLen ([] : List g.flag) (by simp) n g.initial []
      target (List.Sublist.refl target) hder (by simpa using hnN)
  have hτnil : τ = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen : τ.length ≤ 0 := by
      simpa using hτsub.length_le
    omega
  subst τ
  have hbounded :
      StackBoundedDerivesIn g (N + K + N) m
        [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa using hbounded0
  have hder_m :
      g.DerivesIn m [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    StackBoundedDerivesIn.to_derivesIn hbounded
  have hn_le_m : n ≤ m := hmin m hder_m
  have hmn : m = n := by omega
  subst m
  obtain ⟨trace, htrace, hlen, hhead, hlast, htraceBound⟩ :=
    exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn hbounded
  have hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N := by
    intro i hi
    exact htraceBound (trace.get ⟨i, hi⟩) (List.get_mem trace ⟨i, hi⟩)
  have hcard :=
    minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound_lengthBound
      (g := g) (L := L) (B := N + K + N) hNF htrace hlen hhead hlast hmin
      htargetLen hstack
  refine ⟨trace, htrace, hlen, hhead, hlast, hstack, ?_⟩
  omega

theorem boundedStackGrammar_derives_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ}
    {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    ∃ bw₁ bw₂ : List (symbol T (BoundedStackNT g B)),
      boundedSentential? B w₁ = some bw₁ ∧
      boundedSentential? B w₂ = some bw₂ ∧
      grammar_derives (boundedStackGrammar g B) bw₁ bw₂ := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with ⟨rfl, hw₁⟩
      obtain ⟨bw, hbw⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) hw₁
      exact ⟨bw, bw, hbw, hbw, Relation.ReflTransGen.refl⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hw₂⟩
      obtain ⟨bw₁, bw, hbw₁, hbw, hder⟩ := ih hprev
      have hw : sententialMaxStackHeight w ≤ B :=
        StackBoundedDerivesIn.final_maxStackHeight_le hprev
      obtain ⟨cw, bw₂, hcw, hbw₂, htran⟩ :=
        boundedStackGrammar_transforms_of_indexed_transforms
          (g := g) (B := B) hstep hw hw₂
      have hsame : bw = cw := by
        apply Option.some.inj
        rw [← hbw, hcw]
      subst cw
      exact ⟨bw₁, bw₂, hbw₁, hbw₂, hder.tail htran⟩

/-- Sentential-form bridge between the finite bounded-stack grammar and stack-bounded
indexed derivations, for any fixed successful bounded encodings of the endpoints. -/
theorem boundedStackGrammar_derives_iff_exists_stackBoundedDerivesIn_of_boundedSentential
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {w₁ w₂ : List g.ISym}
    {bw₁ bw₂ : List (symbol T (BoundedStackNT g B))}
    (hbw₁ : boundedSentential? (g := g) B w₁ = some bw₁)
    (hbw₂ : boundedSentential? (g := g) B w₂ = some bw₂) :
    grammar_derives (boundedStackGrammar g B) bw₁ bw₂ ↔
      ∃ n, StackBoundedDerivesIn g B n w₁ w₂ := by
  constructor
  · intro hder
    obtain ⟨n, hbounded⟩ :=
      exists_stackBoundedDerivesIn_of_boundedStackGrammar_derives
        (g := g) (B := B) hder
    have herase₁ := eraseBoundedSentential_of_boundedSentential? hbw₁
    have herase₂ := eraseBoundedSentential_of_boundedSentential? hbw₂
    exact ⟨n, by simpa [herase₁, herase₂] using hbounded⟩
  · rintro ⟨n, hbounded⟩
    obtain ⟨cw₁, cw₂, hcw₁, hcw₂, hder⟩ :=
      boundedStackGrammar_derives_of_stackBoundedDerivesIn
        (g := g) (B := B) hbounded
    have hcw₁eq : cw₁ = bw₁ := by
      apply Option.some.inj
      rw [← hcw₁, hbw₁]
    have hcw₂eq : cw₂ = bw₂ := by
      apply Option.some.inj
      rw [← hcw₂, hbw₂]
    subst cw₁
    subst cw₂
    exact hder

/-- Initial-form specialization of
`boundedStackGrammar_derives_iff_exists_stackBoundedDerivesIn_of_boundedSentential`. -/
theorem boundedStackGrammar_derives_from_initial_iff_exists_stackBoundedDerivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {w : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hbw : boundedSentential? (g := g) B w = some bw) :
    grammar_derives (boundedStackGrammar g B)
        [symbol.nonterminal (boundedStackGrammar g B).initial] bw ↔
      ∃ n, StackBoundedDerivesIn g B n [ISym.indexed g.initial []] w := by
  have hstart :
      boundedSentential? (g := g) B [ISym.indexed g.initial []] =
        some [symbol.nonterminal (boundedStackGrammar g B).initial] := by
    simp [boundedStackGrammar, boundedSentential?, boundedSymbol?]
  exact
    boundedStackGrammar_derives_iff_exists_stackBoundedDerivesIn_of_boundedSentential
      (g := g) (B := B) hstart hbw

/-- A reachable bounded encoding of an erased finite surface gives a stack-bounded indexed
prefix derivation to that erased surface. -/
theorem exists_stackBoundedDerivesIn_eraseSurfaceForm_of_boundedStackGrammar_reachable
    {g : IndexedGrammar T} [Fintype g.flag] {K B : ℕ}
    {surface : SurfaceForm g K} {bw : List (symbol T (BoundedStackNT g B))}
    (hbw : boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw)
    (hder : grammar_derives (boundedStackGrammar g B)
      [symbol.nonterminal (boundedStackGrammar g B).initial] bw) :
    ∃ n, StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
      (eraseSurfaceForm surface) := by
  exact
    (boundedStackGrammar_derives_from_initial_iff_exists_stackBoundedDerivesIn
      (g := g) (B := B) hbw).mp hder

/-- Erasing a finite surface whose visible stacks are bounded by `K` can be translated into
any bounded-stack grammar whose stack bound is at least `K`. -/
theorem exists_boundedSentential?_eraseSurfaceForm_of_le
    {g : IndexedGrammar T} {K B : ℕ} (surface : SurfaceForm g K)
    (hKB : K ≤ B) :
    ∃ bw : List (symbol T (BoundedStackNT g B)),
      boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw := by
  exact exists_boundedSentential?_of_sententialMaxStackHeight_le
    (g := g) (B := B)
    (le_trans (eraseSurfaceForm_maxStackHeight_le surface) hKB)

/-- The bounded-grammar sentential forms obtained by erasing length-bounded finite surfaces
and translating them into an arbitrary fixed bounded-stack grammar form a finite set. -/
theorem finite_boundedSentential_image_of_boundedSurfaceForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B L : ℕ} :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      ∃ surface : SurfaceForm g K,
        surface ∈ boundedSurfaceForms g L K ∧
          boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  classical
  let encodeSurface : SurfaceForm g K → List (symbol T (BoundedStackNT g B)) :=
    fun surface =>
      match boundedSentential? (g := g) B (eraseSurfaceForm surface) with
      | some bw => bw
      | none => []
  have hfinite :=
    (boundedSurfaceForms_finite g L K).image encodeSurface
  apply hfinite.subset
  intro bw hbw
  rcases hbw with ⟨surface, hsurface, henc⟩
  exact ⟨surface, hsurface, by simp [encodeSurface, henc]⟩

/-- The bounded-grammar sentential forms obtained by erasing target-compatible finite surfaces
and translating them into an arbitrary fixed bounded-stack grammar form a finite set. -/
theorem finite_boundedSentential_image_of_targetCompatibleBoundedSurfaceForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B : ℕ} (target : List T) :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      ∃ surface : SurfaceForm g K,
        surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
          boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  classical
  let encodeSurface : SurfaceForm g K → List (symbol T (BoundedStackNT g B)) :=
    fun surface =>
      match boundedSentential? (g := g) B (eraseSurfaceForm surface) with
      | some bw => bw
      | none => []
  have hfinite :=
    (targetCompatibleBoundedSurfaceForms_finite g target K).image encodeSurface
  apply hfinite.subset
  intro bw hbw
  rcases hbw with ⟨surface, hsurface, henc⟩
  exact ⟨surface, hsurface, by simp [encodeSurface, henc]⟩

/-- The reachable part of the length-bounded finite surface frontier is finite in any fixed
bounded-stack grammar. This is the prefix side of the finite saturation argument. -/
theorem finite_reachable_boundedSentential_image_of_boundedSurfaceForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B L : ℕ} :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      (∃ surface : SurfaceForm g K,
        surface ∈ boundedSurfaceForms g L K ∧
          boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw) ∧
        grammar_derives (boundedStackGrammar g B)
          [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  exact
    finite_boundedSentential_image_of_boundedSurfaceForms_at_bound
      (g := g) (K := K) (B := B) (L := L) |>.subset
        (by
          intro bw hbw
          exact hbw.1)

/-- The reachable part of the target-compatible finite surface frontier is finite in any
fixed bounded-stack grammar. -/
theorem finite_reachable_boundedSentential_image_of_targetCompatibleBoundedSurfaceForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B : ℕ} (target : List T) :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      (∃ surface : SurfaceForm g K,
        surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
          boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw) ∧
        grammar_derives (boundedStackGrammar g B)
          [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  exact
    finite_boundedSentential_image_of_targetCompatibleBoundedSurfaceForms_at_bound
      (g := g) (K := K) (B := B) target |>.subset
        (by
          intro bw hbw
          exact hbw.1)

/-- Compose a bounded-stack prefix derivation from the initial form with a suffix derivation
from the same frontier representative. -/
theorem boundedStackGrammar_generates_of_prefix_suffix_derives
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {target : List T} {bw : List (symbol T (BoundedStackNT g B))}
    (hprefix : grammar_derives (boundedStackGrammar g B)
      [symbol.nonterminal (boundedStackGrammar g B).initial] bw)
    (hsuffix : grammar_derives (boundedStackGrammar g B) bw
      (target.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)))) :
    target ∈ grammar_language (boundedStackGrammar g B) := by
  simpa [grammar_language, grammar_generates] using hprefix.trans hsuffix

/-- If a suffix representative belongs to the reachable length-bounded frontier, then any
bounded-stack suffix derivation from it generates the target. -/
theorem boundedStackGrammar_generates_of_reachable_boundedSurface_frontier_suffix_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B L : ℕ} {target : List T}
    {bw : List (symbol T (BoundedStackNT g B))}
    (hbw :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g B)) |
          (∃ surface : SurfaceForm g K,
            surface ∈ boundedSurfaceForms g L K ∧
              boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw) ∧
            grammar_derives (boundedStackGrammar g B)
              [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
          Set (List (symbol T (BoundedStackNT g B)))))
    (hsuffix : grammar_derives (boundedStackGrammar g B) bw
      (target.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)))) :
    target ∈ grammar_language (boundedStackGrammar g B) :=
  boundedStackGrammar_generates_of_prefix_suffix_derives
    (g := g) (B := B) hbw.2 hsuffix

/-- Target-compatible variant of
`boundedStackGrammar_generates_of_reachable_boundedSurface_frontier_suffix_at_bound`. -/
theorem boundedStackGrammar_generates_of_reachable_targetCompatible_frontier_suffix_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B : ℕ} {target : List T}
    {bw : List (symbol T (BoundedStackNT g B))}
    (hbw :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g B)) |
          (∃ surface : SurfaceForm g K,
            surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
              boundedSentential? (g := g) B (eraseSurfaceForm surface) = some bw) ∧
            grammar_derives (boundedStackGrammar g B)
              [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
          Set (List (symbol T (BoundedStackNT g B)))))
    (hsuffix : grammar_derives (boundedStackGrammar g B) bw
      (target.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)))) :
    target ∈ grammar_language (boundedStackGrammar g B) :=
  boundedStackGrammar_generates_of_prefix_suffix_derives
    (g := g) (B := B) hbw.2 hsuffix

/-- The bounded-grammar sentential forms obtained by erasing length-bounded finite surfaces
and translating them into the larger stack bound `K + N` form a finite set. This frontier is
uniform in the target word; it depends only on the length bound `L`. -/
theorem finite_boundedSentential_image_of_boundedSurfaceForms
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K N L : ℕ} :
    ({bw : List (symbol T (BoundedStackNT g (K + N))) |
      ∃ surface : SurfaceForm g K,
        surface ∈ boundedSurfaceForms g L K ∧
          boundedSentential? (g := g) (K + N) (eraseSurfaceForm surface) = some bw} :
        Set (List (symbol T (BoundedStackNT g (K + N))))).Finite := by
  classical
  let encodeSurface : SurfaceForm g K → List (symbol T (BoundedStackNT g (K + N))) :=
    fun surface =>
      match boundedSentential? (g := g) (K + N) (eraseSurfaceForm surface) with
      | some bw => bw
      | none => []
  have hfinite :=
    (boundedSurfaceForms_finite g L K).image encodeSurface
  apply hfinite.subset
  intro bw hbw
  rcases hbw with ⟨surface, hsurface, henc⟩
  exact ⟨surface, hsurface, by simp [encodeSurface, henc]⟩

/-- The bounded-grammar sentential forms obtained by erasing target-compatible finite
surfaces and translating them into the larger stack bound `K + N` form a finite set. -/
theorem finite_boundedSentential_image_of_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K N : ℕ} (target : List T) :
    ({bw : List (symbol T (BoundedStackNT g (K + N))) |
      ∃ surface : SurfaceForm g K,
        surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
          boundedSentential? (g := g) (K + N) (eraseSurfaceForm surface) = some bw} :
        Set (List (symbol T (BoundedStackNT g (K + N))))).Finite := by
  classical
  let encodeSurface : SurfaceForm g K → List (symbol T (BoundedStackNT g (K + N))) :=
    fun surface =>
      match boundedSentential? (g := g) (K + N) (eraseSurfaceForm surface) with
      | some bw => bw
      | none => []
  have hfinite :=
    (targetCompatibleBoundedSurfaceForms_finite g target K).image encodeSurface
  apply hfinite.subset
  intro bw hbw
  rcases hbw with ⟨surface, hsurface, henc⟩
  exact ⟨surface, hsurface, by simp [encodeSurface, henc]⟩

/-- Whole-form accepting suffix shrinking compiled into the fixed bounded-stack grammar for
the uniform bound `K + N`. This records the finite grammar derivation supplied by the shrunk
suffix, rather than only the indexed bounded derivation. -/
theorem exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ ys : List g.ISym, ∃ n' : ℕ,
              ∃ bw : List (symbol T (BoundedStackNT g (K + N))),
                n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                surfaceOfTruncatedForm K ys ∈
                  targetCompatibleBoundedSurfaceForms g target K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                boundedSentential? (g := g) (K + N) ys = some bw ∧
                bw ∈
                  ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                    ∃ surface : SurfaceForm g K,
                      surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
                        boundedSentential? (g := g) (K + N)
                          (eraseSurfaceForm surface) = some bw} :
                    Set (List (symbol T (BoundedStackNT g (K + N)))) ) ∧
                grammar_derives (boundedStackGrammar g (K + N)) bw
                  (target.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨ys, n', hn', hrel, hlenEq, htermEq, hntEq, hysBound,
    herase, hsurface, hbounded⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hboundedUniform :
      StackBoundedDerivesIn g (K + N) n' ys
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    StackBoundedDerivesIn.mono_bound (by omega) hbounded
  obtain ⟨bw, btarget, hbw, hbtarget, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := K + N) hboundedUniform
  have hbtargetEq :
      btarget =
        (target.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
    apply Option.some.inj
    rw [← hbtarget]
    simp
  subst btarget
  have hbwm :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g (K + N))) |
          ∃ surface : SurfaceForm g K,
            surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
              boundedSentential? (g := g) (K + N)
                (eraseSurfaceForm surface) = some bw} :
          Set (List (symbol T (BoundedStackNT g (K + N)))) ) :=
    ⟨surfaceOfTruncatedForm K ys, hsurface, by simpa [herase] using hbw⟩
  exact ⟨ys, n', bw, hn', hrel, hlenEq, htermEq, hntEq, hysBound,
    hsurface, herase, hbw, hbwm, hGder⟩

/-- Length-uniform finite-frontier version of
`exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget`.
The compiled suffix starts in a bounded sentential form coming from the finite set of all
surfaces of length at most `L`, independent of the particular target word. -/
theorem exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_lengthBound_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ ys : List g.ISym, ∃ n' : ℕ,
              ∃ bw : List (symbol T (BoundedStackNT g (K + N))),
                n' ≤ trace.length - 1 - i ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                surfaceOfTruncatedForm K ys ∈ boundedSurfaceForms g L K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                boundedSentential? (g := g) (K + N) ys = some bw ∧
                bw ∈
                  ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                    ∃ surface : SurfaceForm g K,
                      surface ∈ boundedSurfaceForms g L K ∧
                        boundedSentential? (g := g) (K + N)
                          (eraseSurfaceForm surface) = some bw} :
                    Set (List (symbol T (BoundedStackNT g (K + N)))) ) ∧
                grammar_derives (boundedStackGrammar g (K + N)) bw
                  (target.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨ys, n', bw, hn', hrel, hlenEq, htermEq, hntEq, hysBound,
    _hsurfaceTarget, herase, hbw, _hbwmTarget, hGder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hsurface :
      surfaceOfTruncatedForm K ys ∈ boundedSurfaceForms g L K := by
    apply surfaceOfTruncatedForm_mem_boundedSurfaceForms
    have hxlen :
        (trace.get ⟨i, hi⟩).length ≤ target.length :=
      accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast hi
    rw [hlenEq]
    exact le_trans hxlen htargetLen
  have hbwm :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g (K + N))) |
          ∃ surface : SurfaceForm g K,
            surface ∈ boundedSurfaceForms g L K ∧
              boundedSentential? (g := g) (K + N)
                (eraseSurfaceForm surface) = some bw} :
          Set (List (symbol T (BoundedStackNT g (K + N)))) ) :=
    ⟨surfaceOfTruncatedForm K ys, hsurface, by simpa [herase] using hbw⟩
  exact ⟨ys, n', bw, hn', hrel, hlenEq, htermEq, hntEq, hysBound,
    hsurface, herase, hbw, hbwm, hGder⟩

/-- Strengthened compiled-suffix theorem retaining the original singleton split, the
replacement singleton split, and the local minimality certificates for each indexed
replacement. This is the finite-grammar form needed by later reachability arguments that
must inspect why the finite representative is a valid shrink of the trace position. -/
theorem exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ parts : List (ℕ × List T),
            ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
            ∃ bw : List (symbol T (BoundedStackNT g (K + N))),
              parts.length = (trace.get ⟨i, hi⟩).length ∧
                (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
                (parts.flatMap fun p => p.2) = target ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  (trace.get ⟨i, hi⟩) parts ∧
                (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
                (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  ys parts' ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                parts'.length = parts.length ∧
                List.Forall₂
                  (fun sp tq =>
                    match sp.1, tq.1 with
                    | ISym.terminal a, ISym.terminal b =>
                        a = b ∧ tq.2 = sp.2
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧
                          tq.2.2 = sp.2.2 ∧
                          tq.2.1 ≤ sp.2.1 ∧
                          τ.Sublist σ ∧
                          τ.length ≤ K ∧
                          g.DerivesIn tq.2.1 [ISym.indexed C τ]
                            (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                          ∀ ρ : List g.flag, ∀ k : ℕ,
                            k ≤ sp.2.1 →
                            g.DerivesIn k [ISym.indexed C ρ]
                              (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                            ρ.Sublist τ → ρ = τ
                    | _, _ => False)
                  ((trace.get ⟨i, hi⟩).zip parts) (ys.zip parts') ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                surfaceOfTruncatedForm K ys ∈
                  targetCompatibleBoundedSurfaceForms g target K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                boundedSentential? (g := g) (K + N) ys = some bw ∧
                bw ∈
                  ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                    ∃ surface : SurfaceForm g K,
                      surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
                        boundedSentential? (g := g) (K + N)
                          (eraseSurfaceForm surface) = some bw} :
                    Set (List (symbol T (BoundedStackNT g (K + N)))) ) ∧
                grammar_derives (boundedStackGrammar g (K + N)) bw
                  (target.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_stackBounded_accepting_derivationTrace_symbols_suffix_shrink_surface_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, ys, parts', hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hlenEq, htermEq, hntEq, hysBound,
    herase, hsurface, hbounded⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hparts'_le_N : (parts'.map fun p => p.1).sum ≤ N := by
    exact le_trans hsum' (by simpa [hsum] using hsuffixBudget)
  have hboundedUniform :
      StackBoundedDerivesIn g (K + N) ((parts'.map fun p => p.1).sum) ys
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    StackBoundedDerivesIn.mono_bound
      (Nat.add_le_add_left hparts'_le_N K) hbounded
  obtain ⟨bw, btarget, hbw, hbtarget, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := K + N) hboundedUniform
  have hbtargetEq :
      btarget =
        (target.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
    apply Option.some.inj
    rw [← hbtarget]
    simp
  subst btarget
  have hbwm :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g (K + N))) |
          ∃ surface : SurfaceForm g K,
            surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
              boundedSentential? (g := g) (K + N)
                (eraseSurfaceForm surface) = some bw} :
          Set (List (symbol T (BoundedStackNT g (K + N)))) ) :=
    ⟨surfaceOfTruncatedForm K ys, hsurface, by simpa [herase] using hbw⟩
  exact ⟨parts, ys, parts', bw, hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hlenEq, htermEq, hntEq, hysBound,
    hsurface, herase, hbw, hbwm, hGder⟩

/-- Length-uniform finite-frontier version of
`exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget_with_minimality`.
It keeps the singleton split and local minimality certificates, while placing the compiled
suffix start in the finite frontier of all surfaces of length at most `L`. -/
theorem exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_lengthBound_budget_with_minimality
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            ∃ parts : List (ℕ × List T),
            ∃ ys : List g.ISym, ∃ parts' : List (ℕ × List T),
            ∃ bw : List (symbol T (BoundedStackNT g (K + N))),
              parts.length = (trace.get ⟨i, hi⟩).length ∧
                (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
                (parts.flatMap fun p => p.2) = target ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  (trace.get ⟨i, hi⟩) parts ∧
                (parts'.map fun p => p.1).sum ≤ (parts.map fun p => p.1).sum ∧
                (parts'.flatMap fun p => p.2) = (parts.flatMap fun p => p.2) ∧
                List.Forall₂
                  (fun s p => g.DerivesIn p.1 [s]
                    (p.2.map fun a => (ISym.terminal a : g.ISym)))
                  ys parts' ∧
                List.Forall₂
                  (fun s t =>
                    match s, t with
                    | ISym.terminal a, ISym.terminal b => a = b
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧ τ.Sublist σ ∧ τ.length ≤ K
                    | _, _ => False)
                  (trace.get ⟨i, hi⟩) ys ∧
                parts'.length = parts.length ∧
                List.Forall₂
                  (fun sp tq =>
                    match sp.1, tq.1 with
                    | ISym.terminal a, ISym.terminal b =>
                        a = b ∧ tq.2 = sp.2
                    | ISym.indexed A σ, ISym.indexed C τ =>
                        A = C ∧
                          tq.2.2 = sp.2.2 ∧
                          tq.2.1 ≤ sp.2.1 ∧
                          τ.Sublist σ ∧
                          τ.length ≤ K ∧
                          g.DerivesIn tq.2.1 [ISym.indexed C τ]
                            (tq.2.2.map fun a => (ISym.terminal a : g.ISym)) ∧
                          ∀ ρ : List g.flag, ∀ k : ℕ,
                            k ≤ sp.2.1 →
                            g.DerivesIn k [ISym.indexed C ρ]
                              (sp.2.2.map fun a => (ISym.terminal a : g.ISym)) →
                            ρ.Sublist τ → ρ = τ
                    | _, _ => False)
                  ((trace.get ⟨i, hi⟩).zip parts) (ys.zip parts') ∧
                ys.length = (trace.get ⟨i, hi⟩).length ∧
                sententialTerminals ys =
                  sententialTerminals (trace.get ⟨i, hi⟩) ∧
                sententialNonterminalCount ys =
                  sententialNonterminalCount (trace.get ⟨i, hi⟩) ∧
                sententialMaxStackHeight ys ≤ K ∧
                surfaceOfTruncatedForm K ys ∈ boundedSurfaceForms g L K ∧
                eraseSurfaceForm (surfaceOfTruncatedForm K ys) = ys ∧
                boundedSentential? (g := g) (K + N) ys = some bw ∧
                bw ∈
                  ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                    ∃ surface : SurfaceForm g K,
                      surface ∈ boundedSurfaceForms g L K ∧
                        boundedSentential? (g := g) (K + N)
                          (eraseSurfaceForm surface) = some bw} :
                    Set (List (symbol T (BoundedStackNT g (K + N)))) ) ∧
                grammar_derives (boundedStackGrammar g (K + N)) bw
                  (target.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget_with_minimality
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget
  obtain ⟨parts, ys, parts', bw, hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hlenEq, htermEq, hntEq, hysBound,
    _hsurfaceTarget, herase, hbw, _hbwmTarget, hGder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  have hsurface :
      surfaceOfTruncatedForm K ys ∈ boundedSurfaceForms g L K := by
    apply surfaceOfTruncatedForm_mem_boundedSurfaceForms
    have hxlen :
        (trace.get ⟨i, hi⟩).length ≤ target.length :=
      accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast hi
    rw [hlenEq]
    exact le_trans hxlen htargetLen
  have hbwm :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g (K + N))) |
          ∃ surface : SurfaceForm g K,
            surface ∈ boundedSurfaceForms g L K ∧
              boundedSentential? (g := g) (K + N)
                (eraseSurfaceForm surface) = some bw} :
          Set (List (symbol T (BoundedStackNT g (K + N)))) ) :=
    ⟨surfaceOfTruncatedForm K ys, hsurface, by simpa [herase] using hbw⟩
  exact ⟨parts, ys, parts', bw, hpartsLen, hsum, hflat, hparts, hsum',
    hflat', hparts', hrel, hpartsLen', hcert, hlenEq, htermEq, hntEq, hysBound,
    hsurface, herase, hbw, hbwm, hGder⟩

theorem exists_boundedStackGrammar_derives_of_global_minimal_derivesIn_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ.Sublist σ → τ = σ) →
            pref.length + n ≤ N →
            ∃ hstack : (pref ++ σ).length ≤ N + (K + N) + N,
              grammar_derives (boundedStackGrammar g (N + (K + N) + N))
                [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)]
                (w.map fun a =>
                  (symbol.terminal a :
                    symbol T (BoundedStackNT g (N + (K + N) + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_global_minimal_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin hbudget
  have hbounded :
      StackBoundedDerivesIn g (N + (K + N) + N) n
        [ISym.indexed A (pref ++ σ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    hK target htargetLen pref hpref n A σ w hwt hder hmin hbudget
  have hstack : (pref ++ σ).length ≤ N + (K + N) + N := by
    have hstart := StackBoundedDerivesIn.initial_maxStackHeight_le hbounded
    simpa using hstart
  obtain ⟨bw₁, bw₂, hbw₁, hbw₂, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := N + (K + N) + N) hbounded
  have hstartSome :
      boundedSentential? (g := g) (N + (K + N) + N)
          [ISym.indexed A (pref ++ σ)] =
        some [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)] := by
    simp only [boundedSentential?]
    rw [boundedSymbol?_indexed_of_le (g := g) (B := N + (K + N) + N)
      (A := A) (σ := pref ++ σ) hstack]
  have htermSome :
      boundedSentential? (g := g) (N + (K + N) + N)
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a =>
          (symbol.terminal a :
            symbol T (BoundedStackNT g (N + (K + N) + N)))) := by
    simp
  have hbw₁ : bw₁ = [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)] := by
    apply Option.some.inj
    rw [← hbw₁, hstartSome]
  have hbw₂ :
      bw₂ =
        (w.map fun a =>
          (symbol.terminal a :
            symbol T (BoundedStackNT g (N + (K + N) + N)))) := by
    apply Option.some.inj
    rw [← hbw₂, htermSome]
  subst bw₁
  subst bw₂
  exact ⟨hstack, hGder⟩

theorem exists_boundedStackGrammar_derives_of_global_minimal_derivesIn_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            (∀ τ : List g.flag, ∀ m : ℕ,
              g.DerivesIn m [ISym.indexed A (pref ++ τ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              τ.Sublist σ → τ = σ) →
            ∃ hstack : (pref ++ σ).length ≤ N + K + n,
              grammar_derives (boundedStackGrammar g (N + K + n))
                [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)]
                (w.map fun a =>
                  (symbol.terminal a : symbol T (BoundedStackNT g (N + K + n)))) := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_global_minimal_derivesIn_target_length_bounded_prefix
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hmin
  have hbounded :
      StackBoundedDerivesIn g (N + K + n) n
        [ISym.indexed A (pref ++ σ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) :=
    hK target htargetLen pref hpref n A σ w hwt hder hmin
  have hstack : (pref ++ σ).length ≤ N + K + n := by
    have hstart := StackBoundedDerivesIn.initial_maxStackHeight_le hbounded
    simpa using hstart
  obtain ⟨bw₁, bw₂, hbw₁, hbw₂, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := N + K + n) hbounded
  have hstartSome :
      boundedSentential? (g := g) (N + K + n)
          [ISym.indexed A (pref ++ σ)] =
        some [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)] := by
    simp only [boundedSentential?]
    rw [boundedSymbol?_indexed_of_le (g := g) (B := N + K + n)
      (A := A) (σ := pref ++ σ) hstack]
  have htermSome :
      boundedSentential? (g := g) (N + K + n)
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + n)))) := by
    simp
  have hbw₁ : bw₁ = [symbol.nonterminal (A, ⟨pref ++ σ, hstack⟩)] := by
    apply Option.some.inj
    rw [← hbw₁, hstartSome]
  have hbw₂ :
      bw₂ =
        (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + n)))) := by
    apply Option.some.inj
    rw [← hbw₂, htermSome]
  subst bw₁
  subst bw₂
  exact ⟨hstack, hGder⟩

theorem exists_boundedStackGrammar_derives_of_derivesIn_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            ∃ m : ℕ, ∃ τ : List g.flag,
              τ.Sublist σ ∧ τ.length ≤ K ∧
              (∃ hstack : (pref ++ τ).length ≤ N + K + m,
                grammar_derives (boundedStackGrammar g (N + K + m))
                  [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)]
                  (w.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (N + K + m))))) ∧
              ∀ ρ : List g.flag, ∀ k : ℕ,
                g.DerivesIn k [ISym.indexed A (pref ++ ρ)]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                ρ.Sublist τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder
  obtain ⟨m, τ, hτsub, hτlen, hbounded, hτmin⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder
  have hstack : (pref ++ τ).length ≤ N + K + m := by
    simp [List.length_append]
    omega
  obtain ⟨bw₁, bw₂, hbw₁, hbw₂, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := N + K + m) hbounded
  have hstartSome :
      boundedSentential? (g := g) (N + K + m)
          [ISym.indexed A (pref ++ τ)] =
        some [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    simp only [boundedSentential?]
    rw [boundedSymbol?_indexed_of_le (g := g) (B := N + K + m)
      (A := A) (σ := pref ++ τ) hstack]
  have htermSome :
      boundedSentential? (g := g) (N + K + m)
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + m)))) := by
    simp
  have hbw₁ : bw₁ = [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    apply Option.some.inj
    rw [← hbw₁, hstartSome]
  have hbw₂ :
      bw₂ =
        (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + m)))) := by
    apply Option.some.inj
    rw [← hbw₂, htermSome]
  subst bw₁
  subst bw₂
  exact ⟨m, τ, hτsub, hτlen, ⟨hstack, hGder⟩, hτmin⟩

theorem exists_boundedStackGrammar_derives_of_derivesIn_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N : ℕ) (target : List T) :
    ∃ K : ℕ,
      ∀ pref : List g.flag,
        pref.length ≤ N →
        ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w.Sublist target →
          g.DerivesIn n [ISym.indexed A (pref ++ σ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) →
          pref.length + n ≤ N →
          ∃ m : ℕ, ∃ τ : List g.flag,
            m ≤ n ∧ τ.Sublist σ ∧ τ.length ≤ K ∧
            ∃ hstack : (pref ++ τ).length ≤ N + K + N,
              grammar_derives (boundedStackGrammar g (N + K + N))
                [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)]
                (w.map fun a =>
                  (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_bounded_prefix_budget
      (g := g) hNF N target
  refine ⟨K, ?_⟩
  intro pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτsub, hτlen, hbounded⟩ :=
    hK pref hpref n A σ w hwt hder hbudget
  have hstack : (pref ++ τ).length ≤ N + K + N := by
    simp [List.length_append]
    omega
  obtain ⟨bw₁, bw₂, hbw₁, hbw₂, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := N + K + N) hbounded
  have hstartSome :
      boundedSentential? (g := g) (N + K + N)
          [ISym.indexed A (pref ++ τ)] =
        some [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    simp only [boundedSentential?]
    rw [boundedSymbol?_indexed_of_le (g := g) (B := N + K + N)
      (A := A) (σ := pref ++ τ) hstack]
  have htermSome :
      boundedSentential? (g := g) (N + K + N)
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
    simp
  have hbw₁ : bw₁ = [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    apply Option.some.inj
    rw [← hbw₁, hstartSome]
  have hbw₂ :
      bw₂ =
        (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
    apply Option.some.inj
    rw [← hbw₂, htermSome]
  subst bw₁
  subst bw₂
  exact ⟨m, τ, hm_le, hτsub, hτlen, hstack, hGder⟩

theorem exists_boundedStackGrammar_derives_of_derivesIn_target_length_bounded_prefix_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w.Sublist target →
            g.DerivesIn n [ISym.indexed A (pref ++ σ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            pref.length + n ≤ N →
            ∃ m : ℕ, ∃ τ : List g.flag,
              m ≤ n ∧ τ.Sublist σ ∧ τ.length ≤ K ∧
              ∃ hstack : (pref ++ τ).length ≤ N + K + N,
                grammar_derives (boundedStackGrammar g (N + K + N))
                  [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)]
                  (w.map fun a =>
                    (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτsub, hτlen, hbounded⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder hbudget
  have hstack : (pref ++ τ).length ≤ N + K + N := by
    simp [List.length_append]
    omega
  obtain ⟨bw₁, bw₂, hbw₁, hbw₂, hGder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := N + K + N) hbounded
  have hstartSome :
      boundedSentential? (g := g) (N + K + N)
          [ISym.indexed A (pref ++ τ)] =
        some [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    simp only [boundedSentential?]
    rw [boundedSymbol?_indexed_of_le (g := g) (B := N + K + N)
      (A := A) (σ := pref ++ τ) hstack]
  have htermSome :
      boundedSentential? (g := g) (N + K + N)
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
    simp
  have hbw₁ : bw₁ = [symbol.nonterminal (A, ⟨pref ++ τ, hstack⟩)] := by
    apply Option.some.inj
    rw [← hbw₁, hstartSome]
  have hbw₂ :
      bw₂ =
        (w.map fun a =>
          (symbol.terminal a : symbol T (BoundedStackNT g (N + K + N)))) := by
    apply Option.some.inj
    rw [← hbw₂, htermSome]
  subst bw₁
  subst bw₂
  exact ⟨m, τ, hm_le, hτsub, hτlen, hstack, hGder⟩

theorem boundedStackGrammar_generates_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ} {w : List T}
    (h : StackBoundedDerivesIn g B n
      [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    w ∈ grammar_language (boundedStackGrammar g B) := by
  obtain ⟨bw₁, bw₂, hstart, hterm, hder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := B) h
  have hstartSome :
      boundedSentential? B [ISym.indexed g.initial []] =
        some [symbol.nonterminal ((boundedStackGrammar g B).initial)] := by
    simp [boundedStackGrammar, boundedSentential?, boundedSymbol?]
  have hbw₁ : bw₁ = [symbol.nonterminal ((boundedStackGrammar g B).initial)] := by
    apply Option.some.inj
    rw [← hstart, hstartSome]
  have htermSome :
      boundedSentential? B
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) := by
    simp
  have hbw₂ : bw₂ =
      w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)) := by
    apply Option.some.inj
    rw [← hterm, htermSome]
  subst bw₁
  subst bw₂
  simpa [grammar_language, grammar_generates] using hder

theorem boundedStackGrammar_derives_of_stackBounded_certificate
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ}
    {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield.StackBounded g B A σ w) :
    grammar_derives (boundedStackGrammar g B)
      [symbol.nonterminal (A, ⟨σ, NFYield.StackBounded.stack_length_le h⟩)]
      (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) := by
  obtain ⟨n, hbounded⟩ :=
    NFYield.StackBounded.exists_stackBoundedDerivesIn (g := g) h
  obtain ⟨bw₁, bw₂, hstart, hterm, hder⟩ :=
    boundedStackGrammar_derives_of_stackBoundedDerivesIn
      (g := g) (B := B) hbounded
  have hstartSome :
      boundedSentential? B [ISym.indexed A σ] =
        some [symbol.nonterminal
          (A, ⟨σ, NFYield.StackBounded.stack_length_le h⟩)] := by
    simp [boundedSentential?, boundedSymbol?, NFYield.StackBounded.stack_length_le h]
  have htermSome :
      boundedSentential? B
          (w.map fun a => (ISym.terminal a : g.ISym)) =
        some (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) := by
    simp
  have hbw₁ :
      bw₁ = [symbol.nonterminal
        (A, ⟨σ, NFYield.StackBounded.stack_length_le h⟩)] := by
    apply Option.some.inj
    rw [← hstart, hstartSome]
  have hbw₂ :
      bw₂ = w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B)) := by
    apply Option.some.inj
    rw [← hterm, htermSome]
  subst bw₁
  subst bw₂
  exact hder

theorem boundedStackGrammar_generates_of_stackBounded_certificate
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ} {w : List T}
    (h : NFYield.StackBounded g B g.initial [] w) :
    w ∈ grammar_language (boundedStackGrammar g B) := by
  obtain ⟨n, hbounded⟩ :=
    NFYield.StackBounded.exists_stackBoundedDerivesIn (g := g) h
  exact boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded

theorem exists_boundedStackGrammar_generates_of_certificate
    {g : IndexedGrammar T} [Fintype g.flag] {w : List T}
    (h : NFYield g g.initial [] w) :
    ∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B) := by
  obtain ⟨B, hboundedCert⟩ := NFYield.exists_stackBounded (g := g) h
  exact ⟨B, boundedStackGrammar_generates_of_stackBounded_certificate (g := g) hboundedCert⟩

theorem exists_boundedStackGrammar_generates_iff_certificate
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List T} :
    (∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B)) ↔
      NFYield g g.initial [] w := by
  constructor
  · rintro ⟨B, hw⟩
    exact (NFYield.generates_iff_isNormalForm (g := g) hNF).mp
      (boundedStackGrammar_language_subset_language (g := g) (B := B) w hw)
  · intro hcert
    exact exists_boundedStackGrammar_generates_of_certificate (g := g) hcert

theorem exists_boundedStackGrammar_generates_iff_stackBounded_certificate
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List T} :
    (∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B)) ↔
      ∃ K, NFYield.StackBounded g K g.initial [] w := by
  rw [exists_boundedStackGrammar_generates_iff_certificate (g := g) hNF]
  constructor
  · exact NFYield.exists_stackBounded
  · rintro ⟨K, hbounded⟩
    exact NFYield.StackBounded.toNFYield hbounded

/-- Budgeted finite-core wrapper for normal-form grammars.

If an accepting derivation is shortest and its length is at most `N`, then a single
bounded-stack grammar with bound `N + K + N` generates the target.  The bound `K` depends
only on the grammar, `N`, and the target length bound `L`, not on the particular derivation.
-/
theorem exists_bound_boundedStackGrammar_generates_of_minimal_derivesIn_target_length_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ n : ℕ,
          g.DerivesIn n [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ m,
            g.DerivesIn m [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
          n ≤ N →
          target ∈ grammar_language (boundedStackGrammar g (N + K + N)) := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n hder hmin hnN
  obtain ⟨m, τ, hm_le, hτsub, _hτlen, hbounded0⟩ :=
    hK target htargetLen ([] : List g.flag) (by simp) n g.initial []
      target (List.Sublist.refl target) hder (by simpa using hnN)
  have hτnil : τ = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen : τ.length ≤ 0 := by
      simpa using hτsub.length_le
    omega
  subst τ
  have hbounded :
      StackBoundedDerivesIn g (N + K + N) m
        [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa using hbounded0
  have hder_m :
      g.DerivesIn m [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    StackBoundedDerivesIn.to_derivesIn hbounded
  have hn_le_m : n ≤ m := hmin m hder_m
  have hmn : m = n := by omega
  subst m
  exact boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := N + K + N) hbounded

theorem boundedStackGrammar_language_iff_exists_stackBoundedDerivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ} {w : List T} :
    w ∈ grammar_language (boundedStackGrammar g B) ↔
      ∃ n, StackBoundedDerivesIn g B n
        [ISym.indexed g.initial []]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
  constructor
  · intro hw
    have hder :
        grammar_derives (boundedStackGrammar g B)
          [symbol.nonterminal (boundedStackGrammar g B).initial]
          (w.map fun a => (symbol.terminal a : symbol T (BoundedStackNT g B))) := by
      simpa [grammar_language, grammar_generates] using hw
    obtain ⟨n, hbounded⟩ :=
      exists_stackBoundedDerivesIn_of_boundedStackGrammar_derives
        (g := g) (B := B) hder
    refine ⟨n, ?_⟩
    simpa [boundedStackGrammar] using hbounded
  · rintro ⟨n, hbounded⟩
    exact boundedStackGrammar_generates_of_stackBoundedDerivesIn
      (g := g) (B := B) hbounded

theorem exists_bounded_isDerivationTrace_of_boundedStackGrammar_language
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ} {w : List T}
    (hw : w ∈ grammar_language (boundedStackGrammar g B)) :
    ∃ n, ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
  obtain ⟨n, hbounded⟩ :=
    (boundedStackGrammar_language_iff_exists_stackBoundedDerivesIn
      (g := g) (B := B) (w := w)).mp hw
  obtain ⟨trace, htrace, hlen, hhead, hlast, hbound⟩ :=
    exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn hbounded
  exact ⟨n, trace, htrace, hlen, hhead, hlast, hbound⟩

theorem boundedStackGrammar_language_iff_exists_bounded_isDerivationTrace
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ} {w : List T} :
    w ∈ grammar_language (boundedStackGrammar g B) ↔
      ∃ n, ∃ trace : List (List g.ISym),
        IsDerivationTrace g trace ∧
        trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
        ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
  constructor
  · exact exists_bounded_isDerivationTrace_of_boundedStackGrammar_language
  · rintro ⟨n, trace, htrace, hlen, hhead, hlast, hbound⟩
    exact boundedStackGrammar_generates_of_stackBoundedDerivesIn
      (g := g) (B := B)
      (stackBoundedDerivesIn_of_bounded_isDerivationTrace
        htrace hlen hhead hlast hbound)

theorem boundedStackGrammar_language_mono {g : IndexedGrammar T}
    [Fintype g.flag] {B C : ℕ} (hBC : B ≤ C) :
    ∀ w, w ∈ grammar_language (boundedStackGrammar g B) →
      w ∈ grammar_language (boundedStackGrammar g C) := by
  intro w hw
  obtain ⟨n, hbounded⟩ :=
    (boundedStackGrammar_language_iff_exists_stackBoundedDerivesIn
      (g := g) (B := B) (w := w)).mp hw
  exact boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := C)
    (StackBoundedDerivesIn.mono_bound hBC hbounded)

theorem boundedStackGrammar_generates_of_derivesIn_of_intermediate_stackBound
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []]
        (w.map fun a => (ISym.terminal a : g.ISym)) i x →
        sententialMaxStackHeight x ≤ B) :
    w ∈ grammar_language (boundedStackGrammar g B) :=
  boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := B)
    (stackBoundedDerivesIn_of_derivesIn_of_intermediate_stackBound
      (g := g) (B := B) h hstack)

theorem boundedStackGrammar_generates_of_derivesIn_isNormalForm_initial_stackBound
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {B n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (hstart : sententialMaxStackHeight ([ISym.indexed g.initial []] : List g.ISym) ≤ B) :
    w ∈ grammar_language (boundedStackGrammar g (B + n)) :=
  boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := B + n)
    (stackBoundedDerivesIn_of_derivesIn_isNormalForm_initial_stackBound
      (g := g) hNF h hstart)

theorem boundedStackGrammar_generates_of_derivesIn_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    w ∈ grammar_language (boundedStackGrammar g n) :=
  boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := n)
    (stackBoundedDerivesIn_of_accepting_derivesIn_isNormalForm hNF h)

theorem boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {N n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (hn : n ≤ N) :
    w ∈ grammar_language (boundedStackGrammar g N) :=
  boundedStackGrammar_generates_of_stackBoundedDerivesIn
    (g := g) (B := N)
    (stackBoundedDerivesIn_of_accepting_derivesIn_isNormalForm_steps_le hNF h hn)

/-- Generated-word form of the late-window replacement bridge, compiled back into a fixed
bounded-stack grammar.

For a generated target, choose a shortest accepting trace and then a least stack bound `B`
among traces of that length. Let `C = |boundedSurfaceForms g L P|`. If the visible prefix
before the late `C`-window is `P`-bounded, and every shrunken high-stack context in that
window is reachable within prefix bound `Bpre`, then the target is generated by the single
bounded-stack grammar with bound `max (P + C) (Bpre + C)`.

This packages the existing dichotomy into the form needed by the final finite normal-form
core: the remaining premise is exactly the bounded-prefix reachability obligation for the
shrunken contexts. -/
theorem exists_bound_boundedStackGrammar_generates_of_late_window_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
        ∃ n B : ℕ, ∃ trace : List (List g.ISym),
          IsDerivationTrace g trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn n [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ m,
              g.DerivesIn m [ISym.indexed g.initial []]
                (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
            (∀ C' : ℕ,
              (∃ trace' : List (List g.ISym),
                IsDerivationTrace g trace' ∧
                  trace'.length = n + 1 ∧
                  trace'.head? = some [ISym.indexed g.initial []] ∧
                  trace'.getLast? =
                    some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  ∀ j (hj : j < trace'.length),
                    sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
                B ≤ C') ∧
            ∀ Bpre : ℕ,
              (∀ k (hk : k < trace.length),
                k < trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
                i ≤ trace.length - 1 -
                      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η pref σ τ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η = pref ++ σ →
                    pref.length ≤ P →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v →
                    τ.Sublist σ →
                    τ.length ≤ K →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A (pref ++ τ)] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g
                    (max
                      (P + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card)
                      (Bpre + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_shorter_reachable_max_stack
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  let Csurf := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  let Bfinal := max (P + Csurf) (Bpre + Csurf)
  have htraceBoundMem :
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
    rw [← hi]
    exact hbound i.1 i.2
  have hbounded :
      StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_of_bounded_isDerivationTrace
      (g := g) htrace hlen hhead hlast htraceBoundMem
  have htargetB : target ∈ grammar_language (boundedStackGrammar g B) :=
    boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded
  by_cases hgt : P + Csurf < B
  · have hdich :
        n < Csurf ∨ B ≤ Bpre + Csurf := by
      exact hK target htargetLen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre
        (by
          intro k hk hlt
          exact hbeforeBound k hk (by simpa [Csurf] using hlt))
        (by simpa [Csurf] using hgt)
        (by
          intro i hi hlow hup hhigh A η pref σ τ u v hmem hη hpref hηmax hctx
            hτsub hτlen
          exact hreachable i hi
            (by simpa [Csurf] using hlow)
            (by simpa [Csurf] using hup)
            hhigh A η pref σ τ u v hmem hη hpref hηmax hctx hτsub hτlen)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g Csurf) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      exact boundedStackGrammar_language_mono
        (g := g) (B := Csurf) (C := Bfinal) (by omega) target htargetC
    · exact boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB
  · exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) (by omega) target htargetB

/-- Generated-word form of the canonical late-window replacement bridge.

Compared with `exists_bound_boundedStackGrammar_generates_of_late_window_reachability`, the
reachability obligation is only for contexts obtained from a selected maximum stack `η` by
replacing its suffix after the visible `P`-prefix, namely `η.take P ++ τ`. -/
theorem exists_bound_boundedStackGrammar_generates_of_late_window_canonical_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
        ∃ n B : ℕ, ∃ trace : List (List g.ISym),
          IsDerivationTrace g trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn n [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ m,
              g.DerivesIn m [ISym.indexed g.initial []]
                (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
            (∀ C' : ℕ,
              (∃ trace' : List (List g.ISym),
                IsDerivationTrace g trace' ∧
                  trace'.length = n + 1 ∧
                  trace'.head? = some [ISym.indexed g.initial []] ∧
                  trace'.getLast? =
                    some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  ∀ j (hj : j < trace'.length),
                    sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
                B ≤ C') ∧
            ∀ Bpre : ℕ,
              (∀ k (hk : k < trace.length),
                k < trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
                i ≤ trace.length - 1 -
                      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g
                    (max
                      (P + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card)
                      (Bpre + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_shorter_reachable_canonical_max_stack
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  let Csurf := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  let Bfinal := max (P + Csurf) (Bpre + Csurf)
  have htraceBoundMem :
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
    rw [← hi]
    exact hbound i.1 i.2
  have hbounded :
      StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_of_bounded_isDerivationTrace
      (g := g) htrace hlen hhead hlast htraceBoundMem
  have htargetB : target ∈ grammar_language (boundedStackGrammar g B) :=
    boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded
  by_cases hgt : P + Csurf < B
  · have hdich :
        n < Csurf ∨ B ≤ Bpre + Csurf := by
      exact hK target htargetLen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre
        (by
          intro k hk hlt
          exact hbeforeBound k hk (by simpa [Csurf] using hlt))
        (by simpa [Csurf] using hgt)
        (by
          intro i hi hlow hup hhigh A η τ u v hmem hηmax hctx hτsub hτlen
          exact hreachable i hi
            (by simpa [Csurf] using hlow)
            (by simpa [Csurf] using hup)
            hhigh A η τ u v hmem hηmax hctx hτsub hτlen)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g Csurf) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      exact boundedStackGrammar_language_mono
        (g := g) (B := Csurf) (C := Bfinal) (by omega) target htargetC
    · exact boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB
  · exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) (by omega) target htargetB

/-- Generated-word form of the certified canonical late-window bridge.

For a generated target, this packages the shortest/minimal-stack accepting trace together
with the certified late-window dichotomy. The remaining reachability premise receives the
actual suffix chosen by the shrinker and its `NFYield` certificate. -/
theorem exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
        ∃ n B : ℕ, ∃ trace : List (List g.ISym),
          IsDerivationTrace g trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            g.DerivesIn n [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ m,
              g.DerivesIn m [ISym.indexed g.initial []]
                (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
            (∀ C' : ℕ,
              (∃ trace' : List (List g.ISym),
                IsDerivationTrace g trace' ∧
                  trace'.length = n + 1 ∧
                  trace'.head? = some [ISym.indexed g.initial []] ∧
                  trace'.getLast? =
                    some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                  ∀ j (hj : j < trace'.length),
                    sententialMaxStackHeight (trace'.get ⟨j, hj⟩) ≤ C') →
                B ≤ C') ∧
            ∀ Bpre : ℕ,
              (∀ k (hk : k < trace.length),
                k < trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
                i ≤ trace.length - 1 -
                      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ : List g.flag,
                  ∀ u v : List g.ISym, ∀ q m : ℕ, ∀ w : List T, ∀ n' : ℕ,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    w.Sublist target →
                    w.length ≤ L →
                    q ≤ trace.length - 1 - i →
                    m ≤ q →
                    m ≤ trace.length - 1 - i →
                    n' ≤ trace.length - 1 - i →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A (η.take P ++ τ) w →
                    g.DerivesIn n' (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g
                    (max
                      (P + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card)
                      (Bpre + (Set.Finite.toFinset
                        (boundedSurfaceForms_finite g L P)).card))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_canonical_max_stack
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  let Csurf := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  let Bfinal := max (P + Csurf) (Bpre + Csurf)
  have htraceBoundMem :
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
    rw [← hi]
    exact hbound i.1 i.2
  have hbounded :
      StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
        (target.map fun a => (ISym.terminal a : g.ISym)) :=
    stackBoundedDerivesIn_of_bounded_isDerivationTrace
      (g := g) htrace hlen hhead hlast htraceBoundMem
  have htargetB : target ∈ grammar_language (boundedStackGrammar g B) :=
    boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded
  by_cases hgt : P + Csurf < B
  · have hdich :
        n < Csurf ∨ B ≤ Bpre + Csurf := by
      exact hK target htargetLen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre
        (by
          intro k hk hlt
          exact hbeforeBound k hk (by simpa [Csurf] using hlt))
        (by simpa [Csurf] using hgt)
        (by
          intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt
            hwlen hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
          exact hreachable i hi
            (by simpa [Csurf] using hlow)
            (by simpa [Csurf] using hup)
            hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen hq hm
            hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g Csurf) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      exact boundedStackGrammar_language_mono
        (g := g) (B := Csurf) (C := Bfinal) (by omega) target htargetC
    · exact boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB
  · exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) (by omega) target htargetB

theorem exists_minimal_accepting_derivesIn_with_boundedStackGrammar_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T}
    (hgen : g.Generates w) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      w.length ≤ n ∧
      w ∈ grammar_language (boundedStackGrammar g n) ∧
      n + 1 ≤
        (Set.Finite.toFinset (boundedSententialForms_finite g w.length n)).card := by
  obtain ⟨n, hder, hmin, hlen, hcard⟩ :=
    exists_minimal_accepting_derivesIn_with_boundedSententialForms_card
      (g := g) hNF hgen
  exact ⟨n, hder, hmin, hlen,
    boundedStackGrammar_generates_of_derivesIn_isNormalForm hNF hder, hcard⟩

/-- Every generated word of a finite-flag normal-form indexed grammar is generated by one of
the concrete fixed-bound compiled grammars. The bound may depend on the accepting derivation;
the remaining global inclusion still needs a uniform LBA/search argument. -/
theorem exists_boundedStackGrammar_generates_of_generates_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List T} (hgen : g.Generates w) :
    ∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B) := by
  obtain ⟨n, hder⟩ := (generates_iff_exists_derivesIn g w).mp hgen
  exact ⟨n, boundedStackGrammar_generates_of_derivesIn_isNormalForm hNF hder⟩

theorem language_eq_iUnion_boundedStackGrammar_language_of_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) :
    g.Language = fun w => ∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B) := by
  ext w
  constructor
  · intro hw
    exact exists_boundedStackGrammar_generates_of_generates_isNormalForm
      (g := g) hNF hw
  · rintro ⟨B, hw⟩
    exact boundedStackGrammar_language_subset_language (g := g) (B := B) w hw

end IndexedGrammar
