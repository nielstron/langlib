module

public import Langlib.Grammars.Indexed.NormalForm.Bounds
public import Langlib.Grammars.Indexed.NormalForm.ParseTree
public import Langlib.Grammars.Indexed.NormalForm.ParseTreeShrinking
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

theorem sententialMaxStackHeight_le_of_boundedSentential?
    {g : IndexedGrammar T} {B : ℕ}
    {w : List g.ISym} {w' : List (symbol T (BoundedStackNT g B))}
    (h : boundedSentential? B w = some w') :
    sententialMaxStackHeight w ≤ B := by
  have herase := eraseBoundedSentential_of_boundedSentential? h
  rw [← herase]
  exact sententialMaxStackHeight_eraseBoundedSentential_le w'

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

/-- Removing one indexed symbol from a bounded sentential context preserves the same max-stack
bound on the surrounding context. -/
theorem sententialMaxStackHeight_context_without_indexed_le {g : IndexedGrammar T}
    {B : ℕ} {u v : List g.ISym} {A : g.nt} {η : List g.flag}
    (h : sententialMaxStackHeight (u ++ [ISym.indexed A η] ++ v) ≤ B) :
    sententialMaxStackHeight (u ++ v) ≤ B := by
  simp only [sententialMaxStackHeight_append, sententialMaxStackHeight_indexed] at h ⊢
  omega

/-- Equality-oriented version of `sententialMaxStackHeight_context_without_indexed_le`. -/
theorem sententialMaxStackHeight_context_without_indexed_le_of_eq {g : IndexedGrammar T}
    {B : ℕ} {ys u v : List g.ISym} {A : g.nt} {η : List g.flag}
    (hctx : ys = u ++ [ISym.indexed A η] ++ v)
    (hys : sententialMaxStackHeight ys ≤ B) :
    sententialMaxStackHeight (u ++ v) ≤ B := by
  exact sententialMaxStackHeight_context_without_indexed_le
    (g := g) (B := B) (u := u) (v := v) (A := A) (η := η)
    (by simpa [hctx] using hys)

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

theorem StackBoundedDerivesIn.initial_sententialStackHeight_le
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    sententialStackHeight w₁ ≤ sententialNonterminalCount w₁ * B :=
  sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
    h.initial_maxStackHeight_le

theorem StackBoundedDerivesIn.final_sententialStackHeight_le
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    sententialStackHeight w₂ ≤ sententialNonterminalCount w₂ * B :=
  sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
    h.final_maxStackHeight_le

theorem StackBoundedDerivesIn.initial_encodeSentential_length_le'
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    (encodeSentential w₁).length ≤ w₁.length + sententialNonterminalCount w₁ * (B + 1) :=
  encodeSentential_length_le_length_add_nonterminalCount_mul_succ_of_maxStackHeight_le
    h.initial_maxStackHeight_le

theorem StackBoundedDerivesIn.final_encodeSentential_length_le'
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    (encodeSentential w₂).length ≤ w₂.length + sententialNonterminalCount w₂ * (B + 1) :=
  encodeSentential_length_le_length_add_nonterminalCount_mul_succ_of_maxStackHeight_le
    h.final_maxStackHeight_le

theorem StackBoundedDerivesIn.initial_encodeSentential_length_le
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    (encodeSentential w₁).length ≤ w₁.length * (B + 2) :=
  encodeSentential_length_le_of_maxStackHeight_le h.initial_maxStackHeight_le

theorem StackBoundedDerivesIn.final_encodeSentential_length_le
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    (encodeSentential w₂).length ≤ w₂.length * (B + 2) :=
  encodeSentential_length_le_of_maxStackHeight_le h.final_maxStackHeight_le

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

/-- Counted bounded-stack grammar derivations erase to counted stack-bounded indexed
derivations with the same number of steps. -/
theorem stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ}
    {w₁ w₂ : List (symbol T (BoundedStackNT g B))}
    (h : grammar_derivesIn (boundedStackGrammar g B) n w₁ w₂) :
    StackBoundedDerivesIn g B n
      (eraseBoundedSentential w₁) (eraseBoundedSentential w₂) := by
  induction n generalizing w₂ with
  | zero =>
      rcases h with rfl
      exact ⟨rfl, sententialMaxStackHeight_eraseBoundedSentential_le w₁⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨eraseBoundedSentential w, ih hprev,
        indexed_transforms_of_boundedStackGrammar_transforms hstep,
        sententialMaxStackHeight_eraseBoundedSentential_le w₂⟩

/-- Initial-form counted bridge from the finite bounded-stack grammar back to the indexed
grammar, for a fixed successful bounded encoding of the endpoint. -/
theorem stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ}
    {w : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hbw : boundedSentential? (g := g) B w = some bw)
    (h : grammar_derivesIn (boundedStackGrammar g B) n
      [symbol.nonterminal (boundedStackGrammar g B).initial] bw) :
    StackBoundedDerivesIn g B n [ISym.indexed g.initial []] w := by
  have hbounded :=
    stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn
      (g := g) (B := B) h
  have herase := eraseBoundedSentential_of_boundedSentential? hbw
  simpa [boundedStackGrammar, herase] using hbounded

/-- Existential step-budget form of
`stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential`. -/
theorem exists_stackBoundedDerivesIn_le_of_boundedStackGrammar_derivesIn_initial_boundedSentential
    {g : IndexedGrammar T} [Fintype g.flag] {B i : ℕ}
    {w : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hbw : boundedSentential? (g := g) B w = some bw)
    (h : ∃ p : ℕ, p ≤ i ∧
      grammar_derivesIn (boundedStackGrammar g B) p
        [symbol.nonterminal (boundedStackGrammar g B).initial] bw) :
    ∃ p : ℕ, p ≤ i ∧
      StackBoundedDerivesIn g B p [ISym.indexed g.initial []] w := by
  rcases h with ⟨p, hpi, hp⟩
  exact ⟨p, hpi,
    stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential
      (g := g) (B := B) hbw hp⟩

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

theorem exists_encoded_bounded_isDerivationTrace_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} {B n : ℕ} {w₁ w₂ : List g.ISym}
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
      trace.length = n + 1 ∧
      trace.head? = some w₁ ∧
      trace.getLast? = some w₂ ∧
      (∀ x ∈ trace, sententialMaxStackHeight x ≤ B) ∧
      ∀ x ∈ trace, (encodeSentential x).length ≤ x.length * (B + 2) := by
  obtain ⟨trace, htrace, hlen, hhead, hlast, hbound⟩ :=
    exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn h
  exact ⟨trace, htrace, hlen, hhead, hlast, hbound,
    fun x hx => encodeSentential_length_le_of_maxStackHeight_le (hbound x hx)⟩

theorem exists_flatBounded_accepting_isDerivationTrace_of_stackBoundedDerivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {w : List T}
    (h : StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      (∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
      ∀ i (hi : i < trace.length),
        (encodeSentential (trace.get ⟨i, hi⟩)).length ≤ w.length * (B + 2) := by
  obtain ⟨trace, htrace, hlen, hhead, hlast, hbound⟩ :=
    exists_bounded_isDerivationTrace_of_stackBoundedDerivesIn h
  have hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B := by
    intro i hi
    exact hbound _ (List.get_mem trace ⟨i, hi⟩)
  exact ⟨trace, htrace, hlen, hhead, hlast, hstack,
    fun i hi =>
      accepting_derivationTrace_get_encodeSentential_length_le_of_isNormalForm_stackBound
        hNF htrace hlast hstack hi⟩

theorem exists_flatLengthBounded_accepting_isDerivationTrace_of_stackBoundedDerivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B L n : ℕ} {w : List T} (hwlen : w.length ≤ L)
    (h : StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      (∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
      ∀ i (hi : i < trace.length),
        (encodeSentential (trace.get ⟨i, hi⟩)).length ≤ L * (B + 2) := by
  obtain ⟨trace, htrace, hlen, hhead, hlast, hstack, hflat⟩ :=
    exists_flatBounded_accepting_isDerivationTrace_of_stackBoundedDerivesIn_isNormalForm
      hNF h
  exact ⟨trace, htrace, hlen, hhead, hlast, hstack,
    fun i hi => le_trans (hflat i hi) (Nat.mul_le_mul_right (B + 2) hwlen)⟩

theorem exists_bounded_accepting_flatTrace_of_stackBoundedDerivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B L n : ℕ} {w : List T} (hwlen : w.length ≤ L)
    (h : StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ trace : List (List g.ISym),
    ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
      IsDerivationTrace g trace ∧
      ftrace = flatTrace trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      ftrace.length = n + 1 ∧
      (∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
      ftrace.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      ftrace.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin ftrace.length,
        ftrace.get i ∈ boundedFlatForms g (L * (B + 2))) ∧
      (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
        FlatTransforms g
          (ftrace.get ⟨i, by omega⟩)
          (ftrace.get ⟨i + 1, hi⟩)) ∧
      FlatDerives g
        (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) := by
  obtain ⟨trace, htrace, hlen, hhead, hlast, hstack, hflat⟩ :=
    exists_flatLengthBounded_accepting_isDerivationTrace_of_stackBoundedDerivesIn_isNormalForm
      hNF hwlen h
  refine ⟨trace, flatTrace trace, htrace, rfl, hlen, hhead, hlast, ?_, hstack, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [flatTrace_length] using hlen
  · simp [hhead]
  · simp [hlast]
  · intro i
    have hiTrace : i.1 < trace.length := by
      simpa [flatTrace_length] using i.2
    rw [flatTrace_get trace hiTrace]
    exact hflat i.1 hiTrace
  · intro i hi
    exact flatTrace_get_flatTransforms_of_isDerivationTrace htrace hi
  · have hder :=
      flatDerives_encode_of_isDerivationTrace_head_last
        (g := g) htrace hhead hlast
    simpa using hder

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

/-- Split a bounded derivation at a fixed step count. -/
theorem stackBoundedDerivesIn_split {g : IndexedGrammar T}
    {B m n : ℕ} {w₁ w₃ : List g.ISym}
    (h : StackBoundedDerivesIn g B (m + n) w₁ w₃) :
    ∃ w₂ : List g.ISym,
      StackBoundedDerivesIn g B m w₁ w₂ ∧
        StackBoundedDerivesIn g B n w₂ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      refine ⟨w₃, ?_, ?_⟩
      · simpa using h
      · exact ⟨rfl, StackBoundedDerivesIn.final_maxStackHeight_le h⟩
  | succ n ih =>
      have h' : StackBoundedDerivesIn g B ((m + n) + 1) w₁ w₃ := by
        simpa [Nat.add_assoc] using h
      rcases h' with ⟨y, hprev, hstep, hw₃⟩
      rcases ih hprev with ⟨w₂, hpre, hsuf⟩
      exact ⟨w₂, hpre, hsuf.tail_of_transforms hstep hw₃⟩

theorem stackBoundedDerivesIn_split_at {g : IndexedGrammar T}
    {B n i : ℕ} {w₁ w₃ : List g.ISym}
    (hi : i ≤ n)
    (h : StackBoundedDerivesIn g B n w₁ w₃) :
    ∃ w₂ : List g.ISym,
      StackBoundedDerivesIn g B i w₁ w₂ ∧
        StackBoundedDerivesIn g B (n - i) w₂ w₃ := by
  have hn : i + (n - i) = n := Nat.add_sub_of_le hi
  rw [← hn] at h
  exact stackBoundedDerivesIn_split (g := g) h

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

/-- Replacing one indexed occurrence by another with the same visible `B`-stack prefix
preserves the full `B`-surface of the surrounding sentential context. -/
theorem surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
    {g : IndexedGrammar T} {B : ℕ} {u v : List g.ISym} {A : g.nt}
    {η ζ : List g.flag} (htake : η.take B = ζ.take B) :
    surfaceOfTruncatedForm B (u ++ [ISym.indexed A η] ++ v) =
      surfaceOfTruncatedForm B (u ++ [ISym.indexed A ζ] ++ v) := by
  simp [surfaceOfTruncatedForm, surfaceOfTruncatedSymbol, ISym.truncateStack, htake]

/-- The stack made of the visible prefix plus the next `K` original flags has the same
`P + K` prefix as the original stack. -/
theorem stack_take_append_drop_take_take_add_eq {α : Type} (η : List α) (P K : ℕ) :
    (η.take P ++ (η.drop P).take K).take (P + K) = η.take (P + K) := by
  by_cases hP : P ≤ η.length
  · have hlen : (η.take P).length = P := List.length_take_of_le hP
    rw [List.take_append, hlen, Nat.add_sub_cancel_left]
    simp [List.take_take]
    exact (List.take_add (l := η) (i := P) (j := K)).symm
  · have hlen : η.length ≤ P := Nat.le_of_not_ge hP
    have hdrop : η.drop P = [] := List.drop_eq_nil_of_le hlen
    have htakeP : η.take P = η := (List.take_eq_self_iff η).mpr hlen
    have htakePK : η.take (P + K) = η := (List.take_eq_self_iff η).mpr (by omega)
    simp [hdrop, htakeP, htakePK]

/-- If the replacement suffix agrees with the original dropped stack on the next `R` visible
flags, then replacing below the first `P` flags preserves the full `P + R` stack prefix. -/
theorem stack_take_append_eq_of_suffix_take_eq {α : Type} {η τ : List α} {P R : ℕ}
    (hP : P ≤ η.length)
    (hτ : τ.take R = (η.drop P).take R) :
    (η.take P ++ τ).take (P + R) = η.take (P + R) := by
  have hlen : (η.take P).length = P := List.length_take_of_le hP
  rw [List.take_append, hlen, Nat.add_sub_cancel_left]
  simp [List.take_take]
  rw [hτ]
  exact (List.take_add (l := η) (i := P) (j := R)).symm

/-- Variable-bound form of `stack_take_append_eq_of_suffix_take_eq`. -/
theorem stack_take_append_take_eq_of_suffix_take_eq {α : Type} {η τ : List α} {P B : ℕ}
    (hP : P ≤ η.length) (hPB : P ≤ B)
    (hτ : τ.take (B - P) = (η.drop P).take (B - P)) :
    (η.take P ++ τ).take B = η.take B := by
  have hB : B = P + (B - P) := by omega
  rw [hB]
  exact stack_take_append_eq_of_suffix_take_eq hP hτ

/-- Full-surface specialization for the canonical replacement that keeps the next `K`
original flags below the visible prefix. -/
theorem surfaceOfTruncatedForm_context_indexed_take_append_drop_take_eq
    {g : IndexedGrammar T} {P K : ℕ} {u v : List g.ISym} {A : g.nt}
    {η : List g.flag} :
    surfaceOfTruncatedForm (P + K) (u ++ [ISym.indexed A η] ++ v) =
      surfaceOfTruncatedForm (P + K)
        (u ++ [ISym.indexed A (η.take P ++ (η.drop P).take K)] ++ v) := by
  exact surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
    (g := g) (A := A) ((stack_take_append_drop_take_take_add_eq η P K).symm)

/-- Full-surface specialization when the replacement suffix preserves the original dropped
stack on the visible suffix prefix. -/
theorem surfaceOfTruncatedForm_context_indexed_eq_of_suffix_take_eq
    {g : IndexedGrammar T} {B P : ℕ} {u v : List g.ISym} {A : g.nt}
    {η τ : List g.flag}
    (hP : P ≤ η.length) (hPB : P ≤ B)
    (hτ : τ.take (B - P) = (η.drop P).take (B - P)) :
    surfaceOfTruncatedForm B (u ++ [ISym.indexed A η] ++ v) =
      surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  exact surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
    (g := g) (A := A)
    ((stack_take_append_take_eq_of_suffix_take_eq hP hPB hτ).symm)

/-- A `P`-surface cannot distinguish a high stack `η` from a canonical replacement that
keeps exactly the visible prefix `η.take P`. -/
theorem surfaceOfTruncatedForm_context_indexed_take_append_eq_of_lt
    {g : IndexedGrammar T} {P : ℕ} {u v : List g.ISym} {A : g.nt}
    {η τ : List g.flag} (hη : P < η.length) :
    surfaceOfTruncatedForm P (u ++ [ISym.indexed A η] ++ v) =
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  have htakeRep : (η.take P ++ τ).take P = η.take P := by
    rw [List.take_append_of_le_length]
    · rw [(List.take_eq_self_iff (η.take P)).mpr]
      rw [List.length_take_of_le (Nat.le_of_lt hη)]
    · rw [List.length_take_of_le (Nat.le_of_lt hη)]
  simp [surfaceOfTruncatedForm, surfaceOfTruncatedSymbol, ISym.truncateStack, htakeRep]

/-- The canonical replacement of a high-stack occurrence has a `P`-surface belonging to the
same target-compatible finite frontier as the original accepting-trace position. -/
theorem surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P : ℕ} {target : List T} {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)))
    {i : ℕ} (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (hη : P < η.length) :
    surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
      targetCompatibleBoundedSurfaceForms g target P := by
  have hsurface :
      surfaceOfTruncatedForm P (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
    rw [hctx]
    exact surfaceOfTruncatedForm_context_indexed_take_append_eq_of_lt hη
  have hmem :
      surfaceOfTruncatedForm P (trace.get ⟨i, hi⟩) ∈
        targetCompatibleBoundedSurfaceForms g target P :=
    accepting_derivationTrace_get_surface_mem_targetCompatibleBoundedSurfaceForms
      (g := g) hNF htrace hlast hi
  rwa [← hsurface]

/-- Length-uniform version of
`surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms`. -/
theorem surfaceOfTruncatedForm_canonical_context_mem_boundedSurfaceForms_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P L : ℕ} {target : List T} {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)))
    (htargetLen : target.length ≤ L)
    {i : ℕ} (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (hη : P < η.length) :
    surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
      boundedSurfaceForms g L P := by
  exact
    targetCompatibleBoundedSurfaceForms_subset_boundedSurfaceForms_lengthBound
      (g := g) (target := target) (L := L) (stackBound := P) htargetLen
      (surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms
        (g := g) hNF htrace hlast hi hctx hη)

/-- Any replacement preserving the first `P` stack flags has the same `P`-surface frontier
membership as the original accepting-trace context. -/
theorem surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P : ℕ} {target : List T} {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)))
    {i : ℕ} (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : ζ.take P = η.take P) :
    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
      targetCompatibleBoundedSurfaceForms g target P := by
  have hsurface :
      surfaceOfTruncatedForm P (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) := by
    rw [hctx]
    exact
      surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
        (g := g) (B := P) (u := u) (v := v) (A := A)
        (η := η) (ζ := ζ) htake.symm
  have hmem :
      surfaceOfTruncatedForm P (trace.get ⟨i, hi⟩) ∈
        targetCompatibleBoundedSurfaceForms g target P :=
    accepting_derivationTrace_get_surface_mem_targetCompatibleBoundedSurfaceForms
      (g := g) hNF htrace hlast hi
  rwa [← hsurface]

/-- Length-uniform version of
`surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms`. -/
theorem surfaceOfTruncatedForm_prefix_preserving_context_mem_boundedSurfaceForms_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P L : ℕ} {target : List T} {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)))
    (htargetLen : target.length ≤ L)
    {i : ℕ} (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : ζ.take P = η.take P) :
    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
      boundedSurfaceForms g L P := by
  exact
    targetCompatibleBoundedSurfaceForms_subset_boundedSurfaceForms_lengthBound
      (g := g) (target := target) (L := L) (stackBound := P) htargetLen
      (surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms
        (g := g) hNF htrace hlast hi hctx htake)

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

/-- If the actual current context and its canonical replacement agree on the full `B` visible
stack prefix, then the current trace position itself supplies the surface-repeat witness needed
by the late-window frontier bridge. -/
theorem exists_canonical_surface_repeat_at_current_of_prefix_bound_take_eq
    {g : IndexedGrammar T} {B P K : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    {i : ℕ} (hi : i < trace.length)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hctxBound : sententialMaxStackHeight (u ++ v) ≤ B)
    (hPK : P + K ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = (η.take P ++ τ).take B) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  refine ⟨i, hi, le_rfl, hprefixBound, hctxBound, hPK, ?_⟩
  rw [hctx]
  exact surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq (g := g) (A := A) htake

/-- Local max-stack bound inside a late window. If all trace positions before `a` are
`P`-bounded and the first trace node is `P`-bounded, then every position in `[a, a + C]`
has stack height at most `P + C + 1`. The extra `1` covers the first step entering the
window from the last pre-window node. -/
theorem isDerivationTrace_get_maxStackHeight_le_late_window_of_before_bound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym} {P C a i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hi : i < trace.length)
    (hai : a ≤ i)
    (hic : i ≤ a + C)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ P + C + 1 := by
  by_cases ha0 : a = 0
  · subst a
    have hder :
        g.DerivesIn i first (trace.get ⟨i, hi⟩) :=
      isDerivationTrace_derivesIn_from_head_get (g := g) htrace hhead hi
    have hheight :=
      derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hder
    omega
  · let b := a - 1
    have hb_lt_a : b < a := by
      dsimp [b]
      omega
    have hb_trace : b < trace.length := by
      dsimp [b]
      omega
    have hbi : b ≤ i := by
      dsimp [b]
      omega
    have hbBound :
        sententialMaxStackHeight (trace.get ⟨b, hb_trace⟩) ≤ P :=
      hbefore b hb_trace hb_lt_a
    have hder :
        g.DerivesIn (i - b) (trace.get ⟨b, hb_trace⟩) (trace.get ⟨i, hi⟩) :=
      isDerivationTrace_derivesIn_get_to_get (g := g) htrace hb_trace hi hbi
    have hheight :=
      derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hder
    omega

/-- Prefix-bound form of
`isDerivationTrace_get_maxStackHeight_le_late_window_of_before_bound`. This is the shape
needed by surface-repeat and bounded-stack prefix-reachability bridges. -/
theorem prefix_maxStackHeight_le_late_window_of_before_bound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym} {P C a i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hic : i ≤ a + C)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) :
    ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P + C + 1 := by
  intro k hk hki
  by_cases hka : k < a
  · have hkP := hbefore k hk hka
    omega
  · exact
      isDerivationTrace_get_maxStackHeight_le_late_window_of_before_bound
        (g := g) hNF htrace hhead hfirstBound hk (Nat.le_of_not_gt hka)
        (by omega) hbefore

/-- Late-window version of
`exists_canonical_surface_repeat_at_current_of_prefix_bound_take_eq`. The prefix bound up to
the current late-window position is obtained from the pre-window `P` bound and the local
normal-form stack-growth estimate. -/
theorem exists_canonical_surface_repeat_at_current_of_late_window_take_eq
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C a i : ℕ} {trace : List (List g.ISym)} {first : List g.ISym}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hctxBound : sententialMaxStackHeight (u ++ v) ≤ B)
    (hPK : P + K ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = (η.take P ++ τ).take B) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  have hprefix :
      ∀ k (hk : k < trace.length),
        k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B := by
    intro k hk hki
    exact le_trans
      (prefix_maxStackHeight_le_late_window_of_before_bound
        (g := g) hNF htrace hhead hfirstBound hic hbefore k hk hki)
      hwindowBound
  exact
    exists_canonical_surface_repeat_at_current_of_prefix_bound_take_eq
      (g := g) (B := B) (P := P) (K := K) (trace := trace)
      (u := u) (v := v) (A := A) (η := η) (τ := τ)
      hi hprefix hctxBound hPK hctx htake

/-- Late-window surface-repeat witness with the surrounding-context bound derived from the
current trace node. The remaining explicit stack hypothesis is the actual visible-prefix
agreement between the current stack and the canonical replacement. -/
theorem exists_canonical_surface_repeat_at_current_of_late_window_take_eq_of_context
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C a i : ℕ} {trace : List (List g.ISym)} {first : List g.ISym}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hPK : P + K ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = (η.take P ++ τ).take B) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  have hcurrent :
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B := by
    exact le_trans
      (prefix_maxStackHeight_le_late_window_of_before_bound
        (g := g) hNF htrace hhead hfirstBound hic hbefore i hi le_rfl)
      hwindowBound
  have hctxBound : sententialMaxStackHeight (u ++ v) ≤ B :=
    sententialMaxStackHeight_context_without_indexed_le_of_eq
      (g := g) hctx hcurrent
  exact
    exists_canonical_surface_repeat_at_current_of_late_window_take_eq
      (g := g) hNF htrace hhead hfirstBound hi hic hwindowBound hbefore
      hctxBound hPK hctx htake

/-- Late-window surface-repeat witness for an arbitrary replacement stack.

If the replacement stack `ζ` agrees with the current stack on the full visible `B` prefix,
then the current trace position itself supplies the full-surface repeat. This is the
prefix-preserving analogue of
`exists_canonical_surface_repeat_at_current_of_late_window_take_eq_of_context`. -/
theorem exists_surface_repeat_at_current_of_late_window_take_eq_of_context
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C a i : ℕ} {trace : List (List g.ISym)} {first : List g.ISym}
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hPK : P + K ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = ζ.take B) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A ζ] ++ v) := by
  have hprefix :
      ∀ k (hk : k < trace.length),
        k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B := by
    intro k hk hki
    exact le_trans
      (prefix_maxStackHeight_le_late_window_of_before_bound
        (g := g) hNF htrace hhead hfirstBound hic hbefore k hk hki)
      hwindowBound
  have hcurrent :
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B :=
    hprefix i hi le_rfl
  have hctxBound : sententialMaxStackHeight (u ++ v) ≤ B :=
    sententialMaxStackHeight_context_without_indexed_le_of_eq
      (g := g) hctx hcurrent
  refine ⟨i, hi, le_rfl, hprefix, hctxBound, hPK, ?_⟩
  rw [hctx]
  exact surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
    (g := g) (B := B) (u := u) (v := v) (A := A) htake

/-- Initial-trace late-window surface-repeat witness for an arbitrary replacement stack.

This is the form needed by the finite-frontier bridges: once the replacement stack has the same
full visible `B` prefix as the current stack, the current trace node itself supplies the
required surface repeat. -/
theorem exists_surface_repeat_at_current_of_late_window_context_take_eq
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C i : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length)
    (hic : i ≤ trace.length - 1 - C + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < trace.length - 1 - C → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hPK : P + K ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = ζ.take B) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A ζ] ++ v) := by
  exact
    exists_surface_repeat_at_current_of_late_window_take_eq_of_context
      (g := g) hNF (B := B) (P := P) (K := K) (C := C)
      (a := trace.length - 1 - C) (i := i) (trace := trace)
      (first := [ISym.indexed g.initial []]) htrace hhead (by simp)
      hi hic hwindowBound hbefore hPK hctx htake

/-- Late-window repeat bridge phrased by suffix-prefix preservation. If the replacement suffix
keeps exactly the first `B - P` flags below the visible prefix, then the current trace node has
the same full `B`-surface as the canonical replacement context. -/
theorem exists_canonical_surface_repeat_at_current_of_late_window_suffix_take_eq_of_context
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C a i : ℕ} {trace : List (List g.ISym)} {first : List g.ISym}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hfirstBound : sententialMaxStackHeight first ≤ P)
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hPK : P + K ≤ B)
    (hPη : P ≤ η.length)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (hsuffix : τ.take (B - P) = (η.drop P).take (B - P)) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  have hPB : P ≤ B := le_trans (Nat.le_add_right P (C + 1)) hwindowBound
  exact
    exists_canonical_surface_repeat_at_current_of_late_window_take_eq_of_context
      (g := g) hNF htrace hhead hfirstBound hi hic hwindowBound hbefore hPK hctx
      ((stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm)

/-- Initial-trace form of
`exists_canonical_surface_repeat_at_current_of_late_window_suffix_take_eq_of_context`.

This is the canonical replacement version used when the replacement suffix preserves the
visible suffix prefix below the top `P` stack flags. -/
theorem exists_canonical_surface_repeat_at_current_of_late_window_context_suffix_take_eq
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P K C i : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length)
    (hic : i ≤ trace.length - 1 - C + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < trace.length - 1 - C → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hPK : P + K ≤ B)
    (hPη : P ≤ η.length)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (hsuffix : τ.take (B - P) = (η.drop P).take (B - P)) :
    ∃ r : ℕ, ∃ hr : r < trace.length,
      r ≤ i ∧
        (∀ k (hk : k < trace.length),
          k ≤ r → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B) ∧
        sententialMaxStackHeight (u ++ v) ≤ B ∧
        P + K ≤ B ∧
        surfaceOfTruncatedForm B (trace.get ⟨r, hr⟩) =
          surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) := by
  exact
    exists_canonical_surface_repeat_at_current_of_late_window_suffix_take_eq_of_context
      (g := g) hNF (B := B) (P := P) (K := K) (C := C)
      (a := trace.length - 1 - C) (i := i) (trace := trace)
      (first := [ISym.indexed g.initial []]) htrace hhead (by simp) hi hic
      hwindowBound hbefore hPK hPη hctx hsuffix

/-- Direct stack-bounded prefix bridge for a late-window replacement whose visible stack prefix
matches the current trace stack. This is the lower-level form of the finite-frontier bridge:
the local window bound supplies a `B`-bounded prefix derivation to the replacement context. -/
theorem exists_stackBoundedDerivesIn_late_window_context_take_eq
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B P C a i j : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hij : i ≤ j)
    (hζ : ζ.length ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = ζ.take B) :
    ∃ p : ℕ,
      p ≤ j ∧
        StackBoundedDerivesIn g B p [ISym.indexed g.initial []]
          (u ++ [ISym.indexed A ζ] ++ v) := by
  let ys : List g.ISym := u ++ [ISym.indexed A ζ] ++ v
  have hprefix :
      ∀ k (hk : k < trace.length),
        k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B := by
    intro k hk hki
    exact le_trans
      (prefix_maxStackHeight_le_late_window_of_before_bound
        (g := g) hNF htrace hhead (by simp) hic hbefore k hk hki)
      hwindowBound
  have hcurrent : sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B :=
    hprefix i hi le_rfl
  have hctxBound : sententialMaxStackHeight (u ++ v) ≤ B :=
    sententialMaxStackHeight_context_without_indexed_le_of_eq
      (g := g) hctx hcurrent
  have hysStack : sententialMaxStackHeight ys ≤ B := by
    simpa [ys] using
      sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le
        (g := g) (u := u) (v := v) (A := A) (σ := ζ)
        hctxBound hζ
  have hsurfaceEq :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B ys := by
    rw [hctx]
    simpa [ys] using
      surfaceOfTruncatedForm_context_indexed_eq_of_stack_take_eq
        (g := g) (B := B) (u := u) (v := v) (A := A)
        (η := η) (ζ := ζ) htake
  exact
    exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound_le
      (g := g) (B := B) (trace := trace) (first := [ISym.indexed g.initial []])
      (ys := ys) htrace hhead hi hij hprefix hysStack hsurfaceEq

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

/-- A bounded derivation from an appended sentential form factors into bounded derivations from
the two sides of the append, preserving the same stack bound. -/
theorem stackBoundedDerivesIn_append_split {g : IndexedGrammar T} {B n : ℕ}
    {u v x : List g.ISym}
    (hder : StackBoundedDerivesIn g B n (u ++ v) x) :
    ∃ m k : ℕ, ∃ u' v' : List g.ISym,
      m + k = n ∧
        x = u' ++ v' ∧
        StackBoundedDerivesIn g B m u u' ∧
        StackBoundedDerivesIn g B k v v' := by
  induction n generalizing x with
  | zero =>
      rcases hder with ⟨hx, hbound⟩
      subst x
      exact ⟨0, 0, u, v, rfl, rfl,
        ⟨rfl, sententialMaxStackHeight_le_of_append_left_le hbound⟩,
        ⟨rfl, sententialMaxStackHeight_le_of_append_right_le hbound⟩⟩
  | succ n ih =>
      rcases hder with ⟨y, hprev, hstep, hxbound⟩
      rcases ih hprev with ⟨m, k, u', v', hmk, hy, hu, hv⟩
      subst y
      rcases transforms_append_cases_of_append hstep with hleft | hright
      · rcases hleft with ⟨u'', hstepLeft, hx⟩
        have hu''bound : sententialMaxStackHeight u'' ≤ B :=
          sententialMaxStackHeight_le_of_append_left_le (by simpa [hx] using hxbound)
        refine ⟨m + 1, k, u'', v', ?_, hx, ?_, hv⟩
        · omega
        · exact hu.tail_of_transforms hstepLeft hu''bound
      · rcases hright with ⟨v'', hstepRight, hx⟩
        have hv''bound : sententialMaxStackHeight v'' ≤ B :=
          sententialMaxStackHeight_le_of_append_right_le (by simpa [hx] using hxbound)
        refine ⟨m, k + 1, u', v'', ?_, hx, hu, ?_⟩
        · omega
        · exact hv.tail_of_transforms hstepRight hv''bound

/-- Bounded counted split of an appended terminal derivation. -/
theorem stackBoundedDerivesIn_append_to_terminals_split {g : IndexedGrammar T}
    {B n : ℕ} {u v : List g.ISym} {w : List T}
    (hder : StackBoundedDerivesIn g B n (u ++ v)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ wu wv : List T,
      m + k = n ∧
        w = wu ++ wv ∧
        StackBoundedDerivesIn g B m u
          (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        StackBoundedDerivesIn g B k v
          (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases stackBoundedDerivesIn_append_split (g := g) hder with
    ⟨m, k, u', v', hmk, hx, hu, hv⟩
  rcases append_eq_map_terminal_split (g := g) hx.symm with
    ⟨wu, wv, hw, hu', hv'⟩
  subst u'
  subst v'
  exact ⟨m, k, wu, wv, hmk, hw, hu, hv⟩

/-- Bounded counted split of a terminal derivation from an arbitrary sentential form into
positionwise singleton derivations. -/
theorem stackBoundedDerivesIn_symbols_to_terminals_split {g : IndexedGrammar T}
    {B n : ℕ} {xs : List g.ISym} {w : List T}
    (hder : StackBoundedDerivesIn g B n xs
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ parts : List (ℕ × List T),
      parts.length = xs.length ∧
        (parts.map fun p => p.1).sum = n ∧
        (parts.flatMap fun p => p.2) = w ∧
        List.Forall₂
          (fun s p => StackBoundedDerivesIn g B p.1 [s]
            (p.2.map fun a => (ISym.terminal a : g.ISym)))
          xs parts := by
  induction xs generalizing n w with
  | nil =>
      obtain ⟨hn, htarget⟩ :=
        derivesIn_nil_left_eq (g := g) (StackBoundedDerivesIn.to_derivesIn hder)
      have hw : w = [] := by
        simpa using htarget
      subst n
      subst w
      exact ⟨[], by simp, by simp, by simp, List.Forall₂.nil⟩
  | cons s xs ih =>
      have hder' : StackBoundedDerivesIn g B n ([s] ++ xs)
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
        simpa using hder
      rcases stackBoundedDerivesIn_append_to_terminals_split
          (g := g) (u := [s]) (v := xs) (w := w) hder' with
        ⟨m, k, wu, wv, hmk, hw, hhead, htail⟩
      rcases ih htail with ⟨parts, hlen, hsum, hflat, hparts⟩
      refine ⟨(m, wu) :: parts, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp [hsum, hmk]
      · simp [hw, hflat]
      · exact List.Forall₂.cons hhead hparts

/-- Bounded counted split for a two-symbol terminal derivation. -/
theorem stackBoundedDerivesIn_pair_to_terminals_split {g : IndexedGrammar T}
    {B n : ℕ} {A C : g.nt} {σ τ : List g.flag} {w : List T}
    (hder : StackBoundedDerivesIn g B n [ISym.indexed A σ, ISym.indexed C τ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        StackBoundedDerivesIn g B m [ISym.indexed A σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        StackBoundedDerivesIn g B k [ISym.indexed C τ]
          (v.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    stackBoundedDerivesIn_append_to_terminals_split
      (g := g) (u := [ISym.indexed A σ]) (v := [ISym.indexed C τ]) hder

private theorem stackBounded_singleton_indexed_eq_context_bounds {g : IndexedGrammar T}
    {A C : g.nt} {σ τ : List g.flag} {u v : List g.ISym}
    (h : [ISym.indexed A σ] = u ++ [ISym.indexed C τ] ++ v) :
    u = [] ∧ v = [] ∧ A = C ∧ σ = τ := by
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons x xs =>
        have hlen := congrArg List.length h
        simp at hlen
  subst u
  have h' : [ISym.indexed A σ] = ISym.indexed C τ :: v := by
    simpa using h
  simp at h'
  rcases h' with ⟨⟨hA, hσ⟩, hv⟩
  exact ⟨rfl, hv, hA, hσ⟩

/-- Bounded first-step analysis for a terminal derivation from one indexed nonterminal in normal
form. The recursive premises remain bounded by the original stack bound. -/
theorem stackBoundedDerivesIn_singleton_to_terminals_cases_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : StackBoundedDerivesIn g B (n + 1) [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    (∃ C D : g.nt, ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed C σ, ISym.indexed D σ] ∧
        StackBoundedDerivesIn g B m [ISym.indexed C σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        StackBoundedDerivesIn g B k [ISym.indexed D σ]
          (v.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ C : g.nt,
      σ = f :: ρ ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed C ρ] ∧
        StackBoundedDerivesIn g B n [ISym.indexed C ρ]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ C : g.nt, ∃ f : g.flag,
      g.Transforms [ISym.indexed A σ] [ISym.indexed C (f :: σ)] ∧
        StackBoundedDerivesIn g B n [ISym.indexed C (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ a : T,
      g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a] ∧ n = 0) := by
  have hsplitInput :
      StackBoundedDerivesIn g B (1 + n) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [Nat.add_comm] using hder
  rcases stackBoundedDerivesIn_split (g := g) (m := 1) (n := n) hsplitInput with
    ⟨mid, hfirst, hrest⟩
  rcases hfirst with ⟨pre, hpre, hstep, _hmidBound⟩
  have hpre' : [ISym.indexed A σ] = pre := by
    simpa using hpre.1
  subst pre
  rcases transforms_kind_cases_of_isNormalForm hNF hstep with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A₀, C, D, p, q, τ, _hC, _hD, hw₁, hw₂⟩
    rcases stackBounded_singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed C σ, ISym.indexed D σ] := by
      simpa using hw₂
    subst mid
    rcases stackBoundedDerivesIn_pair_to_terminals_split (g := g) hrest with
      ⟨m, k, u, v, hmk, hw, hleft, hright⟩
    left
    exact ⟨C, D, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
  · rcases hpop with ⟨A₀, C, f, p, q, ρ, _hC, hw₁, hw₂⟩
    rcases stackBounded_singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hσ⟩
    subst p
    subst q
    subst A₀
    have hmid : mid = [ISym.indexed C ρ] := by
      simpa using hw₂
    subst mid
    right
    left
    exact ⟨f, ρ, C, hσ, hstep, hrest⟩
  · rcases hpush with ⟨A₀, C, f, p, q, τ, _hC, hw₁, hw₂⟩
    rcases stackBounded_singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed C (f :: σ)] := by
      simpa using hw₂
    subst mid
    right
    right
    left
    exact ⟨C, f, hstep, hrest⟩
  · rcases hterm with ⟨A₀, a, p, q, τ, hw₁, hw₂⟩
    rcases stackBounded_singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.terminal a] := by
      simpa using hw₂
    subst mid
    right
    right
    right
    exact ⟨a, hstep, derivesIn_terminal_singleton_eq (g := g) hrest.to_derivesIn,
      derivesIn_terminal_singleton_steps_eq_zero (g := g) hrest.to_derivesIn⟩

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

/-- A stack-bounded singleton derivation in normal form has a parse certificate with the same
stack bound. -/
theorem NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm_exact
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (h : StackBoundedDerivesIn g B n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    NFYield.StackBounded g B A σ w := by
  induction n using Nat.strong_induction_on generalizing B A σ w with
  | h n ih =>
      cases n with
      | zero =>
          have heq : [ISym.indexed A σ] =
              w.map fun a => (ISym.terminal a : g.ISym) := by
            simpa using h.1
          cases w with
          | nil => simp at heq
          | cons a w => simp at heq
      | succ n =>
          have hder' : StackBoundedDerivesIn g B (n + 1) [ISym.indexed A σ]
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
            simpa [Nat.succ_eq_add_one] using h
          have hroot : σ.length ≤ B := by
            simpa using StackBoundedDerivesIn.initial_maxStackHeight_le hder'
          have hcases :=
            stackBoundedDerivesIn_singleton_to_terminals_cases_of_isNormalForm
              (g := g) hNF hder'
          rcases hcases with hbin | hpop | hpush | hterm
          · rcases hbin with ⟨C, D, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
            rcases (transforms_singleton_binary_iff_rule_of_isNormalForm
                (g := g) hNF (A := A) (B := C) (C := D) (σ := σ)).mp hstep with
              ⟨r, hr, hlhs, hc, hrhs⟩
            subst w
            have hleftCert : NFYield.StackBounded g B C σ u :=
              ih m (by omega) hleft
            have hrightCert : NFYield.StackBounded g B D σ v :=
              ih k (by omega) hright
            exact NFYield.StackBounded.binary hroot hr hlhs hc hrhs hleftCert hrightCert
          · rcases hpop with ⟨f, ρ, C, hσ, hstep, hrest⟩
            subst σ
            rcases (transforms_singleton_pop_iff_rule_of_isNormalForm
                (g := g) hNF (A := A) (B := C) (f := f) (ρ := ρ)).mp hstep with
              ⟨r, hr, hlhs, hc, hrhs⟩
            have hrestCert : NFYield.StackBounded g B C ρ w :=
              ih n (Nat.lt_succ_self n) hrest
            exact NFYield.StackBounded.pop hroot hr hlhs hc hrhs hrestCert
          · rcases hpush with ⟨C, f, hstep, hrest⟩
            rcases (transforms_singleton_push_iff_rule_of_isNormalForm
                (g := g) hNF (A := A) (B := C) (f := f) (σ := σ)).mp hstep with
              ⟨r, hr, hlhs, hc, hrhs⟩
            have hrestCert : NFYield.StackBounded g B C (f :: σ) w :=
              ih n (Nat.lt_succ_self n) hrest
            exact NFYield.StackBounded.push hroot hr hlhs hc hrhs hrestCert
          · rcases hterm with ⟨a, hstep, hw, _hn⟩
            rcases (transforms_singleton_terminal_iff_rule_of_isNormalForm
                (g := g) hNF (A := A) (σ := σ) (a := a)).mp hstep with
              ⟨r, hr, hlhs, hc, hrhs⟩
            subst w
            exact NFYield.StackBounded.terminal hroot hr hlhs hc hrhs

/-- Compatibility wrapper for older call sites that used the linear counted certificate bound. -/
theorem NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (h : StackBoundedDerivesIn g B n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    NFYield.StackBounded g (B + n) A σ w := by
  exact NFYield.StackBounded.mono_bound (by omega)
    (NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm_exact
      (g := g) hNF h)

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

/-- Target-specific combined branch-rank budget version of the late high-stack locator.

A root certificate embeds the target-compatible visible surfaces into the combined
single-certificate-or-binary-pair target frontier, so any budget dominating that combined
frontier is also a valid late-window budget. -/
theorem
    exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (hcert : NFYield g g.initial [] target)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_target_surface_certificate_rank_items
          (g := g) P Bcert R target)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
            (g := g) P Bcert R target)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt : P + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
          P < sententialMaxStackHeight (trace.get k) := by
  classical
  let Ct :=
    (Set.Finite.toFinset
      (targetCompatibleBoundedSurfaceForms_finite g target P)).card
  have hCtC : Ct ≤ C := by
    have hCtBranch :
        Ct ≤
          (Set.Finite.toFinset
            (NFYield.finite_bounded_target_surface_certificate_rank_items
              (g := g) P Bcert R target)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                (g := g) P Bcert R target)).card := by
      simpa [Ct] using
        NFYield.targetCompatibleBoundedSurfaceForms_card_le_bounded_target_surface_branch_rank_items_card_of_certificate
          (g := g) (P := P) (B := Bcert) (R := R) (target := target) hcert
    exact le_trans hCtBranch hC
  by_cases hn : n < C
  · exact Or.inl hn
  · have hC_le_n : C ≤ n := Nat.le_of_not_gt hn
    have hm : trace.length - 1 - C + Ct < trace.length := by
      omega
    obtain ⟨k, hkLower, hkUpper, hsuffixBudget, hhigh⟩ :=
      exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := P) (N := C) (n := n) (B := B)
        hbeforeBound
        (by simpa [Ct] using hm)
        hgt
    refine Or.inr ⟨k, hkLower, ?_, hsuffixBudget, hhigh⟩
    exact le_trans hkUpper (Nat.add_le_add_left hCtC (trace.length - 1 - C))

/-- Generated-target version of
`exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound`.

For a normal-form grammar, `g.Generates target` supplies the root certificate used to compare
the visible surface frontier with the target combined branch frontier. -/
theorem
    exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (hgen : g.Generates target)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_target_surface_certificate_rank_items
          (g := g) P Bcert R target)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
            (g := g) P Bcert R target)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt : P + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
          P < sententialMaxStackHeight (trace.get k) := by
  exact
    exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (C := C) (n := n)
      (B := B) (trace := trace) (target := target)
      ((NFYield.generates_iff_isNormalForm (g := g) hNF).mp hgen) hC htrace hlen hhead
      hlast hminLength hminBound hbeforeBound hgt

/-- Generated-target card version of the target combined branch-rank high-stack locator.

The late-window budget is exactly the cardinality of the target combined branch frontier. -/
theorem
    exists_high_stack_between_late_target_surface_branch_rank_frontier_card_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (hgen : g.Generates target)
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
          ((Set.Finite.toFinset
            (NFYield.finite_bounded_target_surface_certificate_rank_items
              (g := g) P Bcert R target)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                (g := g) P Bcert R target)).card) →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt :
      P +
          ((Set.Finite.toFinset
            (NFYield.finite_bounded_target_surface_certificate_rank_items
              (g := g) P Bcert R target)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                (g := g) P Bcert R target)).card) <
        B) :
    n <
        (Set.Finite.toFinset
          (NFYield.finite_bounded_target_surface_certificate_rank_items
            (g := g) P Bcert R target)).card +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
              (g := g) P Bcert R target)).card ∨
      ∃ k : Fin trace.length,
        trace.length - 1 -
            ((Set.Finite.toFinset
              (NFYield.finite_bounded_target_surface_certificate_rank_items
                (g := g) P Bcert R target)).card +
              (Set.Finite.toFinset
                (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                  (g := g) P Bcert R target)).card) ≤ k.1 ∧
          k.1 ≤
            trace.length - 1 -
                ((Set.Finite.toFinset
                  (NFYield.finite_bounded_target_surface_certificate_rank_items
                    (g := g) P Bcert R target)).card +
                  (Set.Finite.toFinset
                    (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                      (g := g) P Bcert R target)).card) +
              ((Set.Finite.toFinset
                (NFYield.finite_bounded_target_surface_certificate_rank_items
                  (g := g) P Bcert R target)).card +
                (Set.Finite.toFinset
                  (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                    (g := g) P Bcert R target)).card) ∧
          trace.length - 1 - k.1 ≤
            (Set.Finite.toFinset
              (NFYield.finite_bounded_target_surface_certificate_rank_items
                (g := g) P Bcert R target)).card +
              (Set.Finite.toFinset
                (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
                  (g := g) P Bcert R target)).card ∧
          P < sententialMaxStackHeight (trace.get k) := by
  exact
    exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R)
      (C :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_target_surface_certificate_rank_items
            (g := g) P Bcert R target)).card +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
              (g := g) P Bcert R target)).card)
      (n := n) (B := B) (trace := trace) (target := target) hgen le_rfl
      htrace hlen hhead hlast hminLength hminBound hbeforeBound hgt

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

/-- Enlarged-window version of
`exists_high_stack_between_late_lengthBound_surface_card_or_steps_lt_card_of_minimal_stack_gt_bound`.

The late-window budget `C` may be any number at least as large as the length-uniform visible
surface frontier. This is the form needed when the saturation argument uses a larger finite
frontier, for example one pairing surfaces with parse-certificate items. -/
theorem exists_high_stack_between_late_lengthBound_surface_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {K L C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hC :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L K)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ K)
    (hgt : K + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
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
  have hCtC : Ct ≤ C := le_trans hCtCL (by simpa [CL] using hC)
  by_cases hn : n < C
  · exact Or.inl hn
  · have hC_le_n : C ≤ n := Nat.le_of_not_gt hn
    have hm : trace.length - 1 - C + Ct < trace.length := by
      omega
    obtain ⟨k, hkLower, hkUpper, hsuffixBudget, hhigh⟩ :=
      exists_high_stack_between_late_surface_card_of_minimal_stack_gt_bound
        (g := g) hNF htrace hlen hhead hlast hminLength hminBound
        (K := K) (N := C) (n := n) (B := B)
        hbeforeBound
        (by simpa [Ct] using hm)
        hgt
    refine Or.inr ⟨k, hkLower, ?_, hsuffixBudget, hhigh⟩
    exact le_trans hkUpper (Nat.add_le_add_left hCtC (trace.length - 1 - C))

/-- Rank-frontier budget version of
`exists_high_stack_between_late_lengthBound_surface_budget_or_steps_lt_budget_of_minimal_stack_gt_bound`.

A root parse certificate embeds the visible surface frontier into the length-uniform
surface/certificate/rank frontier, so any budget dominating that rank frontier is also a valid
late-window budget for the high-stack locator. -/
theorem
    exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R L C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hcert : NFYield g g.initial [] target)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt : P + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
          P < sententialMaxStackHeight (trace.get k) := by
  classical
  have hsurfaceRank :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card :=
    NFYield.boundedSurfaceForms_card_le_bounded_length_surface_certificate_rank_items_card_of_certificate
      (g := g) (P := P) (B := Bcert) (L := L) (R := R) htargetLen hcert
  exact
    exists_high_stack_between_late_lengthBound_surface_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
      (g := g) hNF (K := P) (L := L) (C := C) (n := n) (B := B)
      htargetLen (le_trans hsurfaceRank hC) htrace hlen hhead hlast hminLength
      hminBound hbeforeBound hgt

/-- Generated-target version of
`exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound`.

For a normal-form grammar, `g.Generates target` supplies the root certificate used to compare
the visible surface frontier with the length-uniform surface/certificate/rank frontier. -/
theorem
    exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R L C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hgen : g.Generates target)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt : P + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
          P < sententialMaxStackHeight (trace.get k) := by
  exact
    exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (L := L) (C := C)
      (n := n) (B := B) (trace := trace) (target := target) htargetLen
      ((NFYield.generates_iff_isNormalForm (g := g) hNF).mp hgen) hC htrace hlen hhead
      hlast hminLength hminBound hbeforeBound hgt

/-- Generated-target rank-frontier-card version of
`exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound`.

The late-window budget is the cardinality of the finite length-uniform
surface/certificate/rank frontier itself. The generated target supplies the root certificate
used to compare the visible surface frontier with that cardinal. -/
theorem
    exists_high_stack_between_late_lengthBound_surface_certificate_rank_frontier_card_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R L n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hgen : g.Generates target)
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
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P Bcert L R)).card →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt :
      P +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P Bcert L R)).card <
        B) :
    n <
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card ∨
      ∃ k : Fin trace.length,
        trace.length - 1 -
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P Bcert L R)).card ≤ k.1 ∧
          k.1 ≤
            trace.length - 1 -
                (Set.Finite.toFinset
                  (NFYield.finite_bounded_length_surface_certificate_rank_items
                    (g := g) P Bcert L R)).card +
              (Set.Finite.toFinset
                (NFYield.finite_bounded_length_surface_certificate_rank_items
                  (g := g) P Bcert L R)).card ∧
          trace.length - 1 - k.1 ≤
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P Bcert L R)).card ∧
          P < sententialMaxStackHeight (trace.get k) := by
  classical
  have hC :
      (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card ≤
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card := by
    exact le_rfl
  exact
    exists_high_stack_between_late_lengthBound_surface_certificate_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (L := L)
      (C :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card)
      (n := n) (B := B) (trace := trace) (target := target) htargetLen hgen hC
      htrace hlen hhead hlast hminLength hminBound
      hbeforeBound hgt

/-- Generated-target combined branch/rank budget version of the length-uniform high-stack
locator.

The length-uniform combined branch frontier dominates the target-specific combined frontier for
every generated target in the length ball. -/
theorem
    exists_high_stack_between_late_lengthBound_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R L C n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hgen : g.Generates target)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C)
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
      k < trace.length - 1 - C →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt : P + C < B) :
    n < C ∨
      ∃ k : Fin trace.length,
        trace.length - 1 - C ≤ k.1 ∧
          k.1 ≤ trace.length - 1 - C + C ∧
          trace.length - 1 - k.1 ≤ C ∧
          P < sententialMaxStackHeight (trace.get k) := by
  have hTargetC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_target_surface_certificate_rank_items
          (g := g) P Bcert R target)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_target_surface_pair_certificate_rank_items
            (g := g) P Bcert R target)).card ≤ C := by
    exact le_trans
      (NFYield.bounded_target_surface_branch_rank_items_card_le_bounded_length_surface_branch_rank_items_card
        (g := g) (P := P) (B := Bcert) (L := L) (R := R) (target := target)
        htargetLen)
      hC
  exact
    exists_high_stack_between_late_target_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (C := C) (n := n)
      (B := B) (trace := trace) (target := target) hgen hTargetC
      htrace hlen hhead hlast hminLength hminBound hbeforeBound hgt

/-- Generated-target card version of the length-uniform combined branch/rank high-stack locator.

The late-window budget is the cardinality of the finite length-uniform combined branch frontier. -/
theorem
    exists_high_stack_between_late_lengthBound_surface_branch_rank_frontier_card_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P Bcert R L n B : ℕ} {trace : List (List g.ISym)} {target : List T}
    (htargetLen : target.length ≤ L)
    (hgen : g.Generates target)
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
          ((Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P Bcert L R)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                (g := g) P Bcert L R)).card) →
        sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hgt :
      P +
          ((Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P Bcert L R)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                (g := g) P Bcert L R)).card) <
        B) :
    n <
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
              (g := g) P Bcert L R)).card ∨
      ∃ k : Fin trace.length,
        trace.length - 1 -
            ((Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P Bcert L R)).card +
              (Set.Finite.toFinset
                (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                  (g := g) P Bcert L R)).card) ≤ k.1 ∧
          k.1 ≤
            trace.length - 1 -
                ((Set.Finite.toFinset
                  (NFYield.finite_bounded_length_surface_certificate_rank_items
                    (g := g) P Bcert L R)).card +
                  (Set.Finite.toFinset
                    (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                      (g := g) P Bcert L R)).card) +
              ((Set.Finite.toFinset
                (NFYield.finite_bounded_length_surface_certificate_rank_items
                  (g := g) P Bcert L R)).card +
                (Set.Finite.toFinset
                  (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                    (g := g) P Bcert L R)).card) ∧
          trace.length - 1 - k.1 ≤
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P Bcert L R)).card +
              (Set.Finite.toFinset
                (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                  (g := g) P Bcert L R)).card ∧
          P < sententialMaxStackHeight (trace.get k) := by
  exact
    exists_high_stack_between_late_lengthBound_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (L := L)
      (C :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
              (g := g) P Bcert L R)).card)
      (n := n) (B := B) (trace := trace) (target := target) htargetLen hgen le_rfl
      htrace hlen hhead hlast hminLength hminBound
      hbeforeBound hgt

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
              NFYield.StackBounded g (N + K + N) A (pref ++ τ) w := by
  obtain ⟨K, hK⟩ :=
    exists_stackBoundedDerivesIn_of_derivesIn_target_length_bounded_prefix_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref n A σ w hwt hder hbudget
  obtain ⟨m, τ, hm_le, hτsub, hτlen, hbounded⟩ :=
    hK target htargetLen pref hpref n A σ w hwt hder hbudget
  have hcert :
      NFYield.StackBounded g (N + K + N) A (pref ++ τ) w :=
    NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm_exact
      (g := g) hNF hbounded
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
          NFYield.StackBounded g (N + K + N) g.initial [] target := by
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

/-- Whole-stack form of context replacement by bounded suffix shrinking.

At an accepting-trace position, split the selected stack as `η.take N ++ η.drop N`, shrink
only the dropped suffix, and reassemble the accepting suffix derivation. The replacement stack
is a sublist of the original stack, has uniformly bounded length, and preserves the first `N`
visible flags exactly. -/
theorem exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            ∀ A : g.nt, ∀ η : List g.flag, ∀ u v : List g.ISym,
              trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
              ∃ m : ℕ, ∃ ζ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                w.Sublist target ∧ w.length ≤ L ∧
                ζ.Sublist η ∧ ζ.length ≤ N + K ∧ ζ.take N = η.take N ∧
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi A η u v hctx
  let pref : List g.flag := η.take N
  let σ : List g.flag := η.drop N
  have hpref : pref.length ≤ N := by
    simp [pref]
  have hηsplit : pref ++ σ = η := by
    simp [pref, σ]
  have hctx' :
      trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v := by
    simpa [hηsplit] using hctx
  obtain ⟨m, τ, w, n', hwt, hwlen, hτsub, hτlen, hτder, hreplacement, _hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hpref u v hctx'
  let ζ : List g.flag := pref ++ τ
  have hζsub : ζ.Sublist η := by
    have hsub : (pref ++ τ).Sublist (pref ++ σ) :=
      List.Sublist.append (List.Sublist.refl pref) hτsub
    simpa [ζ, hηsplit] using hsub
  have hζlen : ζ.length ≤ N + K := by
    simpa [ζ, List.length_append] using Nat.add_le_add hpref hτlen
  have hζtake : ζ.take N = η.take N := by
    simpa [ζ, pref, σ] using
      NFYield.take_append_sublist_drop_eq_take (σ := η) (τ := τ) (N := N) hτsub
  refine ⟨m, ζ, w, n', hwt, hwlen, hζsub, hζlen, hζtake, ?_, ?_⟩
  · simpa [ζ] using hτder
  · simpa [ζ] using hreplacement

/-- Budget-preserving whole-stack context replacement.

This is the prefix-preserving form of
`exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget`.
The parameter `P` is the preserved visible stack prefix, while `Q` bounds that prefix together
with the remaining trace budget. The replacement keeps the accepting suffix no longer than
the original trace suffix. -/
theorem
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P Q L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ hi : i < trace.length,
            P ≤ Q →
            P + (trace.length - 1 - i) ≤ Q →
            ∀ A : g.nt, ∀ η : List g.flag, ∀ u v : List g.ISym,
              trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
              ∃ q m : ℕ, ∃ τ ζ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                w.Sublist target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ.Sublist (η.drop P) ∧ τ.length ≤ K ∧
                ζ = η.take P ++ τ ∧
                ζ.Sublist η ∧ ζ.length ≤ P + K ∧ ζ.take P = η.take P ∧
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ.Sublist τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_suffix_shrink_replacement_budget
      (g := g) hNF Q L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hPQ hbudget A η u v hctx
  let pref : List g.flag := η.take P
  let σ : List g.flag := η.drop P
  have hprefP : pref.length ≤ P := by
    simp [pref]
  have hprefQ : pref.length ≤ Q := le_trans hprefP hPQ
  have hprefBudget : pref.length + (trace.length - 1 - i) ≤ Q := by
    omega
  have hηsplit : pref ++ σ = η := by
    simp [pref, σ]
  have hctx' :
      trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A (pref ++ σ)] ++ v := by
    simpa [hηsplit] using hctx
  obtain ⟨q, m, τ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
      hτder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi A pref σ hprefQ hprefBudget u v hctx'
  let ζ : List g.flag := pref ++ τ
  have hζeq : ζ = η.take P ++ τ := by
    simp [ζ, pref]
  have hζsub : ζ.Sublist η := by
    have hsub : (pref ++ τ).Sublist (pref ++ σ) :=
      List.Sublist.append (List.Sublist.refl pref) hτsub
    simpa [ζ, hηsplit] using hsub
  have hζlen : ζ.length ≤ P + K := by
    simpa [ζ, List.length_append] using Nat.add_le_add hprefP hτlen
  have hζtake : ζ.take P = η.take P := by
    simpa [ζ, pref, σ] using
      NFYield.take_append_sublist_drop_eq_take (σ := η) (τ := τ) (N := P) hτsub
  refine ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub,
    hτlen, hζeq, hζsub, hζlen, hζtake, ?_, ?_, ?_⟩
  · simpa [ζ] using hτder
  · simpa [ζ] using hreplacement
  · intro ρ k hk hρder hρsub
    exact hτmin ρ k hk (by simpa [pref] using hρder) hρsub

/-- Minimal-stack bridge for prefix-preserving context replacement with a shortened prefix.

The budgeted prefix-preserving shrinker produces a bounded replacement stack `ζ` whose first
`P` flags agree with the original stack. If that concrete replacement context is reachable by
a `Bpre`-bounded prefix no longer than the original trace prefix, then the replacement suffix
can be spliced into the shortest derivation, forcing the least stack bound `B` of that
shortest derivation below `Bpre + n'`. -/
theorem
    exists_bound_minimal_stackBound_le_of_shorter_reachable_indexed_context_prefix_preserving_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P Q L : ℕ) :
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
            ∀ A : g.nt, ∀ η : List g.flag, ∀ u v : List g.ISym, ∀ Bpre : ℕ,
              P ≤ Q →
              P + (trace.length - 1 - i) ≤ Q →
              trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
              (∀ τ ζ : List g.flag,
                τ.Sublist (η.drop P) →
                τ.length ≤ K →
                ζ = η.take P ++ τ →
                ζ.Sublist η →
                ζ.length ≤ P + K →
                ζ.take P = η.take P →
                ∃ p : ℕ,
                  p ≤ i ∧
                    StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                      (u ++ [ISym.indexed A ζ] ++ v)) →
              ∃ q m : ℕ, ∃ τ ζ : List g.flag, ∃ w : List T, ∃ n' : ℕ,
                w.Sublist target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ.Sublist (η.drop P) ∧ τ.length ≤ K ∧
                ζ = η.take P ++ τ ∧
                ζ.Sublist η ∧ ζ.length ≤ P + K ∧ ζ.take P = η.take P ∧
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                (∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ.Sublist τ → ρ = τ) ∧
                B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
      (g := g) hNF P Q L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi A η u v Bpre hPQ hbudget hctx hreachable
  obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
      hζeq, hζsub, hζlen, hζtake, hζder, hreplacement, hτmin⟩ :=
    hK target htargetLen trace htrace hlast i hi hPQ hbudget A η u v hctx
  obtain ⟨p, hp, hpre⟩ :=
    hreachable τ ζ hτsub hτlen hζeq hζsub hζlen hζtake
  have hsteps : p + n' ≤ n := by
    omega
  have hB :
      B ≤ Bpre + n' :=
    minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
      (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
      (w := target) (mid := u ++ [ISym.indexed A ζ] ++ v)
      hminLength hminBound hpre hreplacement hsteps
  exact ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
    hζeq, hζsub, hζlen, hζtake, hζder, hreplacement, hτmin, hB⟩

/-- Max-stack form of the prefix-preserving replacement bridge.

The selected occurrence attains the maximum stack height at the current trace position. The
remaining reachability premise is only about the concrete bounded stack `ζ` produced by the
prefix-preserving shrinker. -/
theorem
    exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_prefix_preserving_shrink_replacement_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P Q L : ℕ) :
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
          ∀ i : ℕ, ∀ hi : i < trace.length, ∀ Bpre : ℕ,
            P ≤ Q →
            P + (trace.length - 1 - i) ≤ Q →
            0 < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
            (∀ A : g.nt, ∀ η τ ζ : List g.flag, ∀ u v : List g.ISym,
              ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
              η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
              τ.Sublist (η.drop P) →
              τ.length ≤ K →
              ζ = η.take P ++ τ →
              ζ.Sublist η →
              ζ.length ≤ P + K →
              ζ.take P = η.take P →
              ∃ p : ℕ,
                p ≤ i ∧
                  StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                    (u ++ [ISym.indexed A ζ] ++ v)) →
            ∃ A : g.nt, ∃ η τ ζ : List g.flag, ∃ u v : List g.ISym,
              ∃ q m : ℕ, ∃ w : List T, ∃ n' : ℕ,
                ISym.indexed A η ∈ trace.get ⟨i, hi⟩ ∧
                η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) ∧
                trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v ∧
                w.Sublist target ∧ w.length ≤ L ∧
                q ≤ trace.length - 1 - i ∧
                m ≤ q ∧
                m ≤ trace.length - 1 - i ∧
                n' ≤ trace.length - 1 - i ∧
                τ.Sublist (η.drop P) ∧ τ.length ≤ K ∧
                ζ = η.take P ++ τ ∧
                ζ.Sublist η ∧ ζ.length ≤ P + K ∧ ζ.take P = η.take P ∧
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) ∧
                g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                  (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                (∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ.Sublist τ → ρ = τ) ∧
                B ≤ Bpre + n' := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_indexed_context_prefix_preserving_shrink_replacement_budget
      (g := g) hNF P Q L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hPQ hbudget hpos hreachable
  obtain ⟨A, η, hmem, hηmax⟩ :=
    exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
      (g := g) (w := trace.get ⟨i, hi⟩) hpos
  rcases List.mem_iff_append.mp hmem with ⟨u, v, hctx0⟩
  have hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v := by
    simpa using hctx0
  obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn', hτsub, hτlen,
      hζeq, hζsub, hζlen, hζtake, hζder, hreplacement, hτmin, hB⟩ :=
    hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
      i hi A η u v Bpre hPQ hbudget hctx
      (by
        intro τ ζ hτsub hτlen hζeq hζsub hζlen hζtake
        exact hreachable A η τ ζ u v hmem hηmax hctx hτsub hτlen hζeq hζsub
          hζlen hζtake)
  exact ⟨A, η, τ, ζ, u, v, q, m, w, n', hmem, hηmax, hctx, hwt, hwlen, hq,
    hm, hmSuffix, hn', hτsub, hτlen, hζeq, hζsub, hζlen, hζtake, hζder,
    hreplacement, hτmin, hB⟩

/-- Late-window max-stack bridge using prefix-preserving replacements.

If the pre-window prefix is `P`-bounded and the least accepting stack bound is above
`P + N`, then a high stack in the late window can be prefix-preservingly shrunk. Whenever the
resulting concrete replacement context is reachable by a shortened `Bpre`-bounded prefix, the
least accepting stack bound is at most `Bpre + N`. -/
theorem
    exists_bound_minimal_stackBound_le_of_late_window_shorter_reachable_prefix_preserving_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P N L : ℕ) :
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
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            B ≤ Bpre + N := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_prefix_preserving_shrink_replacement_budget
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
  obtain ⟨A, η, τ, ζ, u, v, q, m, w, n', hmem, hηmax, hctx, hwt, hwlen,
      hq, hm', hmSuffix, hn', hτsub, hτlen, hζeq, hζsub, hζlen, hζtake,
      hζder, hreplacement, hτmin, hB⟩ :=
    hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
      i.1 i.2 Bpre hP_le hbudget hpos
      (by
        intro A η τ ζ u v hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen hζtake
        exact hreachable i.1 i.2 hiLower hiUpper hhigh A η τ ζ u v
          hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen hζtake)
  have hnN : n' ≤ N := le_trans hn' hsuffixBudget
  omega

/-- Cardinal-budget late-window dichotomy using prefix-preserving replacements.

For `C = |boundedSurfaceForms g L P|`, either the chosen shortest accepting derivation has
fewer than `C` steps, or the prefix-preserving late-window bridge bounds the least accepting
stack height by `Bpre + C`. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_prefix_preserving_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P L : ℕ) :
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
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                ∀ u v : List g.ISym,
                  ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                  η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                  τ.Sublist (η.drop P) →
                  τ.length ≤ K →
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ∨
              B ≤ Bpre +
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card := by
  classical
  let C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_of_shorter_reachable_max_stack_prefix_preserving_shrink_replacement_budget
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
    obtain ⟨A, η, τ, ζ, u, v, q, m, w, n', hmem, hηmax, hctx, hwt, hwlen,
        hq, hm, hmSuffix, hn', hτsub, hτlen, hζeq, hζsub, hζlen, hζtake,
        hζder, hreplacement, hτmin, hB⟩ :=
      hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
        i.1 i.2 Bpre hP_le hbudget hpos
        (by
          intro A η τ ζ u v hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen
            hζtake
          exact hreachable i.1 i.2
            (by simpa [C] using hiLower) (by simpa [C] using hiUpper) hhigh
            A η τ ζ u v hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen hζtake)
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

/-- Certified prefix-preserving late-window dichotomy.

This strengthens
`exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_prefix_preserving_max_stack`
by exposing the concrete prefix-preserving shrinker output before the remaining reachability
premise is invoked. The premise receives the selected replacement stack `ζ`, its local
singleton derivation, the corresponding `NFYield` certificate, and the accepting-suffix
replacement. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_prefix_preserving_max_stack
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
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  g.DerivesIn m [ISym.indexed A ζ]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A ζ w →
                  g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ∨
              B ≤ Bpre +
                (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card := by
  classical
  let C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
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
    obtain ⟨A, η, hmem, hηmax⟩ :=
      exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
        (g := g) (w := trace.get i) hpos
    rcases List.mem_iff_append.mp hmem with ⟨u, v, hctx0⟩
    have hctx : trace.get i = u ++ [ISym.indexed A η] ++ v := by
      simpa using hctx0
    obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
        hτsub, hτlen, hζeq, hζsub, hζlen, hζtake, hζder, hreplacement,
        hτmin⟩ :=
      hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget A η u v hctx
    have hcert : NFYield g A ζ w :=
      NFYield.of_derivesIn_isNormalForm (g := g) hNF hζder
    obtain ⟨p, hp, hpre⟩ :=
      hreachable i.1 i.2
        (by simpa [C] using hiLower)
        (by simpa [C] using hiUpper)
        hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen hq hm hmSuffix
        hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert hreplacement hτmin
    have hsteps : p + n' ≤ n := by
      omega
    have hB :
        B ≤ Bpre + n' :=
      minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
        (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
        (w := target) (mid := u ++ [ISym.indexed A ζ] ++ v)
        hminLength hminBound hpre hreplacement hsteps
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

/-- Arbitrary-budget certified prefix-preserving late-window dichotomy.

This is the same certified bridge as
`exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_prefix_preserving_max_stack`,
but the late-window size is an explicit budget `C`, required only to dominate the
length-uniform visible-surface frontier. Later finite-frontier arguments can instantiate `C`
with a larger combined frontier. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_prefix_preserving_budget_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
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
              k < trace.length - 1 - C →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + C < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - C ≤ i →
              i ≤ trace.length - 1 - C + C →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  g.DerivesIn m [ISym.indexed A ζ]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A ζ w →
                  g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            n < C ∨ B ≤ Bpre + C := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_budget_or_steps_lt_budget_of_minimal_stack_gt_bound
      (g := g) hNF (K := P) (L := L) (C := C) (n := n) (B := B)
      htargetLen hC htrace hlen hhead hlast hminLength hminBound hbeforeBound hgt
  rcases hdich with hn | ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩
  · exact Or.inl hn
  · have hP_le : P ≤ P + C := Nat.le_add_right P C
    have hbudget : P + (trace.length - 1 - i.1) ≤ P + C :=
      Nat.add_le_add_left hsuffixBudget P
    have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
      lt_of_le_of_lt (Nat.zero_le P) hhigh
    obtain ⟨A, η, hmem, hηmax⟩ :=
      exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
        (g := g) (w := trace.get i) hpos
    rcases List.mem_iff_append.mp hmem with ⟨u, v, hctx0⟩
    have hctx : trace.get i = u ++ [ISym.indexed A η] ++ v := by
      simpa using hctx0
    obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
        hτsub, hτlen, hζeq, hζsub, hζlen, hζtake, hζder, hreplacement,
        hτmin⟩ :=
      hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget A η u v hctx
    have hcert : NFYield g A ζ w :=
      NFYield.of_derivesIn_isNormalForm (g := g) hNF hζder
    obtain ⟨p, hp, hpre⟩ :=
      hreachable i.1 i.2 hiLower hiUpper hhigh A η τ ζ u v q m w n'
        hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
        hζlen hζtake hζder hcert hreplacement hτmin
    have hsteps : p + n' ≤ n := by
      omega
    have hB :
        B ≤ Bpre + n' :=
      minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
        (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
        (w := target) (mid := u ++ [ISym.indexed A ζ] ++ v)
        hminLength hminBound hpre hreplacement hsteps
    have hnC : n' ≤ C := le_trans hn' hsuffixBudget
    exact Or.inr (by omega)

/-- Arbitrary-budget combined branch/rank frontier version of the certified late-window
dichotomy.

This is the budgeted counterpart of
`exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_branch_rank_frontier_max_stack`.
The late-window size is an explicit `C`, required to dominate the finite length-uniform
frontier containing both single certificate/rank states and binary pair/rank states. This is the
form needed by saturated branch/rank arguments, where the consuming frontier is enlarged after
the replacement bound is known. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_branch_rank_budget_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L C : ℕ)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
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
              k < trace.length - 1 - C →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + C < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - C ≤ i →
              i ≤ trace.length - 1 - C + C →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  g.DerivesIn m [ISym.indexed A ζ]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A ζ w →
                  g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            n < C ∨ B ≤ Bpre + C := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_branch_rank_budget_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (L := L) (C := C)
      (n := n) (B := B) (trace := trace) (target := target)
      htargetLen hgen hC htrace hlen hhead hlast hminLength hminBound
      hbeforeBound hgt
  rcases hdich with hn | ⟨i, hiLower, hiUpper, hsuffixBudget, hhigh⟩
  · exact Or.inl hn
  · have hP_le : P ≤ P + C := Nat.le_add_right P C
    have hbudget : P + (trace.length - 1 - i.1) ≤ P + C :=
      Nat.add_le_add_left hsuffixBudget P
    have hpos : 0 < sententialMaxStackHeight (trace.get i) :=
      lt_of_le_of_lt (Nat.zero_le P) hhigh
    obtain ⟨A, η, hmem, hηmax⟩ :=
      exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
        (g := g) (w := trace.get i) hpos
    rcases List.mem_iff_append.mp hmem with ⟨u, v, hctx0⟩
    have hctx : trace.get i = u ++ [ISym.indexed A η] ++ v := by
      simpa using hctx0
    obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
        hτsub, hτlen, hζeq, hζsub, hζlen, hζtake, hζder, hreplacement,
        hτmin⟩ :=
      hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget A η u v hctx
    have hcert : NFYield g A ζ w :=
      NFYield.of_derivesIn_isNormalForm (g := g) hNF hζder
    obtain ⟨p, hp, hpre⟩ :=
      hreachable i.1 i.2 hiLower hiUpper hhigh A η τ ζ u v q m w n'
        hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
        hζlen hζtake hζder hcert hreplacement hτmin
    have hsteps : p + n' ≤ n := by
      omega
    have hB :
        B ≤ Bpre + n' :=
      minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
        (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
        (w := target) (mid := u ++ [ISym.indexed A ζ] ++ v)
        hminLength hminBound hpre hreplacement hsteps
    have hnC : n' ≤ C := le_trans hn' hsuffixBudget
    exact Or.inr (by omega)

/-- Combined branch/rank frontier version of the certified prefix-preserving late-window
dichotomy.

The late-window size is the finite length-uniform frontier containing both single
certificate/rank states and binary pair/rank states. For generated targets, the target-specific
combined frontier embeds into this length-uniform one, so the high-stack locator can use this
branch-aware budget directly. -/
theorem
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_branch_rank_frontier_max_stack
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P Bcert L R)).card
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
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
              k < trace.length - 1 - C →
                sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
            P + C < B →
            (∀ i : ℕ, ∀ hi : i < trace.length,
              trace.length - 1 - C ≤ i →
              i ≤ trace.length - 1 - C + C →
              P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
              ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                  ζ = η.take P ++ τ →
                  ζ.Sublist η →
                  ζ.length ≤ P + K →
                  ζ.take P = η.take P →
                  g.DerivesIn m [ISym.indexed A ζ]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  NFYield g A ζ w →
                  g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                    (target.map fun a => (ISym.terminal a : g.ISym)) →
                  (∀ ρ : List g.flag, ∀ k : ℕ,
                    k ≤ q →
                    g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    ρ.Sublist τ → ρ = τ) →
                  ∃ p : ℕ,
                    p ≤ i ∧
                      StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                        (u ++ [ISym.indexed A ζ] ++ v)) →
            n < C ∨ B ≤ Bpre + C := by
  classical
  dsimp only
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P Bcert L R)).card +
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
        (g := g) P Bcert L R)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_accepting_derivationTrace_indexed_context_prefix_preserving_shrink_replacement_budget
      (g := g) hNF P (P + C) L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen n B trace htrace hlen hhead hlast hminLength hminBound
    Bpre hbeforeBound hgt hreachable
  have hdich :=
    exists_high_stack_between_late_lengthBound_surface_branch_rank_frontier_card_or_steps_lt_budget_of_minimal_stack_gt_bound_of_generates
      (g := g) hNF (P := P) (Bcert := Bcert) (R := R) (L := L) (n := n)
      (B := B) (trace := trace) (target := target)
      htargetLen hgen htrace hlen hhead hlast hminLength hminBound
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
    obtain ⟨A, η, hmem, hηmax⟩ :=
      exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
        (g := g) (w := trace.get i) hpos
    rcases List.mem_iff_append.mp hmem with ⟨u, v, hctx0⟩
    have hctx : trace.get i = u ++ [ISym.indexed A η] ++ v := by
      simpa using hctx0
    obtain ⟨q, m, τ, ζ, w, n', hwt, hwlen, hq, hm, hmSuffix, hn',
        hτsub, hτlen, hζeq, hζsub, hζlen, hζtake, hζder, hreplacement,
        hτmin⟩ :=
      hK target htargetLen trace htrace hlast i.1 i.2 hP_le hbudget A η u v hctx
    have hcert : NFYield g A ζ w :=
      NFYield.of_derivesIn_isNormalForm (g := g) hNF hζder
    obtain ⟨p, hp, hpre⟩ :=
      hreachable i.1 i.2
        (by simpa [C] using hiLower)
        (by simpa [C] using hiUpper)
        hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen hq hm hmSuffix
        hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert hreplacement hτmin
    have hsteps : p + n' ≤ n := by
      omega
    have hB :
        B ≤ Bpre + n' :=
      minimal_accepting_stackBound_le_of_stackBounded_prefix_derivesIn_suffix
        (g := g) hNF (n := n) (B := B) (Bpre := Bpre) (p := p) (q := n')
        (w := target) (mid := u ++ [ISym.indexed A ζ] ++ v)
        hminLength hminBound hpre hreplacement hsteps
    have hnC : n' ≤ C := le_trans hn' (by simpa [C] using hsuffixBudget)
    exact Or.inr (by omega)

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

/-- Flat-tape version of
`exists_bound_bounded_accepting_trace_and_surface_bound_of_minimal_derivesIn_target_length_budget`.
Under the same temporary step-budget hypothesis, the produced shortest accepting trace has every
flat encoded sentential form inside the finite tape space of length
`L * ((N + K + N) + 2)`, and its step count is bounded by that finite flat space. -/
theorem exists_bound_flat_accepting_trace_and_flat_bound_of_minimal_derivesIn_target_length_budget
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
            (∀ i (hi : i < trace.length),
              (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
                L * ((N + K + N) + 2)) ∧
            n < (Set.Finite.toFinset
              (boundedFlatForms_finite g (L * ((N + K + N) + 2)))).card := by
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
  obtain ⟨trace, htrace, hlen, hhead, hlast, hstack, hflat⟩ :=
    exists_flatLengthBounded_accepting_isDerivationTrace_of_stackBoundedDerivesIn_isNormalForm
      (g := g) hNF (B := N + K + N) (L := L) htargetLen hbounded
  have hcard :=
    minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
      (g := g) (L := L) (B := N + K + N) hNF htrace hlen hhead hlast hmin
      htargetLen hstack
  refine ⟨trace, htrace, hlen, hhead, hlast, hstack, hflat, ?_⟩
  omega

/-- Fully packaged flat-path version of
`exists_bound_flat_accepting_trace_and_flat_bound_of_minimal_derivesIn_target_length_budget`.
Under the temporary step-budget hypothesis, a shortest accepting derivation yields an indexed
trace and its flat trace, every flat node lies in the finite bounded flat search space, adjacent
flat nodes are one flat grammar step apart, and the derivation length is bounded by that finite
space. -/
theorem exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_budget
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
          ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
            IsDerivationTrace g trace ∧
            ftrace = flatTrace trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? =
              some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            ftrace.length = n + 1 ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N) ∧
            ftrace.head? =
              some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
            ftrace.getLast? =
              some (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            (∀ i : Fin ftrace.length,
              ftrace.get i ∈
                boundedFlatForms g (L * ((N + K + N) + 2))) ∧
            (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
              FlatTransforms g
                (ftrace.get ⟨i, by omega⟩)
                (ftrace.get ⟨i + 1, hi⟩)) ∧
            FlatDerives g
              (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
              (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            n < (Set.Finite.toFinset
              (boundedFlatForms_finite g
                (L * ((N + K + N) + 2)))).card := by
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
  obtain ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives⟩ :=
    exists_bounded_accepting_flatTrace_of_stackBoundedDerivesIn_isNormalForm
      (g := g) hNF (B := N + K + N) (L := L) htargetLen hbounded
  have hcard :=
    minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
      (g := g) (L := L) (B := N + K + N) hNF htrace hlen hhead hlast hmin
      htargetLen hstack
  refine ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives, ?_⟩
  omega

/-- Step-budget flat-path version with the sharper flat tape space from the pop-budget
accounting. Compared with
`exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_budget`, the finite
flat set is bounded by `L + L + (N + L * (N + K + N))`: `N` pays for future pops and
`L * (N + K + N)` pays for live stacks under the produced stack bound. -/
theorem exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_stepFlatBound
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
          ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
            IsDerivationTrace g trace ∧
            ftrace = flatTrace trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? =
              some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            ftrace.length = n + 1 ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N) ∧
            ftrace.head? =
              some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
            ftrace.getLast? =
              some (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            (∀ i : Fin ftrace.length,
              ftrace.get i ∈
                boundedFlatForms g (L + L + (N + L * (N + K + N)))) ∧
            (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
              FlatTransforms g
                (ftrace.get ⟨i, by omega⟩)
                (ftrace.get ⟨i + 1, hi⟩)) ∧
            FlatDerives g
              (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
              (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            n < (Set.Finite.toFinset
              (boundedFlatForms_finite g
                (L + L + (N + L * (N + K + N))))).card := by
  obtain ⟨K, hK⟩ :=
    exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n hder hmin hnN
  obtain ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, _hfbound, hfstep, hfderives, _hcard⟩ :=
    hK target htargetLen n hder hmin hnN
  subst ftrace
  have hboundMem :
      ∀ x ∈ trace, sententialMaxStackHeight x ≤ N + K + N := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
    rw [← hi]
    exact hstack i.1 i.2
  have hfboundStep :
      ∀ i : Fin (flatTrace trace).length,
        (flatTrace trace).get i ∈
          boundedFlatForms g (L + L + (N + L * (N + K + N))) :=
    accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_stepBudget_stackBound_lengthBound
      (g := g) (B := N + K + N) (L := L) (n := n) (N := N)
      hNF htrace hlen hlast htargetLen hboundMem hnN
  have hcard :=
    minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
      (g := g) (L := L) (B := N + K + N) (N := N)
      hNF htrace hlen hhead hlast hmin htargetLen hboundMem hnN
  refine ⟨trace, flatTrace trace, htrace, rfl, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfboundStep, hfstep, hfderives, ?_⟩
  omega

/-- Generated-word version of
`exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_budget`.
The temporary budget is stated as a bound on the selected shortest accepting derivation length,
while the theorem itself chooses that shortest derivation and returns the flat finite-path
certificate. -/
theorem exists_bound_bounded_accepting_flatPath_of_generates_target_length_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
        (∀ n : ℕ,
          g.DerivesIn n [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ m,
            g.DerivesIn m [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
          n ≤ N) →
          ∃ n : ℕ,
          ∃ trace : List (List g.ISym),
          ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
            g.DerivesIn n [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ m,
              g.DerivesIn m [ISym.indexed g.initial []]
                (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) ∧
            IsDerivationTrace g trace ∧
            ftrace = flatTrace trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? =
              some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            ftrace.length = n + 1 ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N) ∧
            ftrace.head? =
              some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
            ftrace.getLast? =
              some (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            (∀ i : Fin ftrace.length,
              ftrace.get i ∈
                boundedFlatForms g (L * ((N + K + N) + 2))) ∧
            (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
              FlatTransforms g
                (ftrace.get ⟨i, by omega⟩)
                (ftrace.get ⟨i + 1, hi⟩)) ∧
            FlatDerives g
              (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
              (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            n < (Set.Finite.toFinset
              (boundedFlatForms_finite g
                (L * ((N + K + N) + 2)))).card := by
  obtain ⟨K, hK⟩ :=
    exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen hbudget
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives, hcard⟩ :=
    hK target htargetLen n hder hmin (hbudget n hder hmin)
  exact ⟨n, trace, ftrace, hder, hmin, htrace, hftrace, hlen, hhead, hlast, hflen,
    hstack, hfhead, hflast, hfbound, hfstep, hfderives, hcard⟩

/-- Generated-word wrapper for
`exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_stepFlatBound`.
It packages the sharper step-budget flat finite set after choosing a shortest accepting
derivation for the generated target. -/
theorem exists_bound_bounded_accepting_flatPath_of_generates_target_length_stepFlatBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        g.Generates target →
        (∀ n : ℕ,
          g.DerivesIn n [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) →
          (∀ m,
            g.DerivesIn m [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
          n ≤ N) →
          ∃ n : ℕ,
          ∃ trace : List (List g.ISym),
          ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
            g.DerivesIn n [ISym.indexed g.initial []]
              (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            (∀ m,
              g.DerivesIn m [ISym.indexed g.initial []]
                (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) ∧
            IsDerivationTrace g trace ∧
            ftrace = flatTrace trace ∧
            trace.length = n + 1 ∧
            trace.head? = some [ISym.indexed g.initial []] ∧
            trace.getLast? =
              some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
            ftrace.length = n + 1 ∧
            (∀ i (hi : i < trace.length),
              sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ N + K + N) ∧
            ftrace.head? =
              some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
            ftrace.getLast? =
              some (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            (∀ i : Fin ftrace.length,
              ftrace.get i ∈
                boundedFlatForms g (L + L + (N + L * (N + K + N)))) ∧
            (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
              FlatTransforms g
                (ftrace.get ⟨i, by omega⟩)
                (ftrace.get ⟨i + 1, hi⟩)) ∧
            FlatDerives g
              (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
              (target.map fun a =>
                (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
            n < (Set.Finite.toFinset
              (boundedFlatForms_finite g
                (L + L + (N + L * (N + K + N))))).card := by
  obtain ⟨K, hK⟩ :=
    exists_bound_bounded_accepting_flatPath_of_minimal_derivesIn_target_length_stepFlatBound
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen hbudget
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives, hcard⟩ :=
    hK target htargetLen n hder hmin (hbudget n hder hmin)
  exact ⟨n, trace, ftrace, hder, hmin, htrace, hftrace, hlen, hhead, hlast, hflen,
    hstack, hfhead, hflast, hfbound, hfstep, hfderives, hcard⟩

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

/-- Counted version of `boundedStackGrammar_derives_of_stackBoundedDerivesIn` for fixed
successful encodings of the endpoints. -/
theorem boundedStackGrammar_derivesIn_of_stackBoundedDerivesIn_of_boundedSentential
    {g : IndexedGrammar T} [Fintype g.flag] {B n : ℕ}
    {w₁ w₂ : List g.ISym}
    {bw₁ bw₂ : List (symbol T (BoundedStackNT g B))}
    (hbw₁ : boundedSentential? (g := g) B w₁ = some bw₁)
    (hbw₂ : boundedSentential? (g := g) B w₂ = some bw₂)
    (h : StackBoundedDerivesIn g B n w₁ w₂) :
    grammar_derivesIn (boundedStackGrammar g B) n bw₁ bw₂ := by
  induction n generalizing w₁ w₂ bw₁ bw₂ with
  | zero =>
      rcases h with ⟨rfl, _hw₁⟩
      have hbw : bw₁ = bw₂ := by
        apply Option.some.inj
        rw [← hbw₁, hbw₂]
      subst bw₂
      exact rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep, hw₂⟩
      have hw : sententialMaxStackHeight w ≤ B :=
        StackBoundedDerivesIn.final_maxStackHeight_le hprev
      obtain ⟨bw, hbw⟩ :=
        exists_boundedSentential?_of_sententialMaxStackHeight_le
          (g := g) (B := B) hw
      have hprevDer :
          grammar_derivesIn (boundedStackGrammar g B) n bw₁ bw :=
        ih hbw₁ hbw hprev
      obtain ⟨cw, dw, hcw, hdw, htran⟩ :=
        boundedStackGrammar_transforms_of_indexed_transforms
          (g := g) (B := B) hstep hw hw₂
      have hcwEq : bw = cw := by
        apply Option.some.inj
        rw [← hbw, hcw]
      subst cw
      have hdwEq : dw = bw₂ := by
        apply Option.some.inj
        rw [← hdw, hbw₂]
      subst dw
      exact ⟨bw, hprevDer, htran⟩

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

/-- The bounded-grammar sentential forms obtained by translating full sentential forms with
bounded length and bounded stack height into an arbitrary fixed bounded-stack grammar form a
finite set. This is the full-context frontier used when the visible surface is not enough to
recover the replacement context. -/
theorem finite_boundedSentential_image_of_boundedSententialForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B L : ℕ} :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      ∃ ys : List g.ISym,
        ys ∈ boundedSententialForms g L K ∧
          boundedSentential? (g := g) B ys = some bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  classical
  let encodeForm : List g.ISym → List (symbol T (BoundedStackNT g B)) :=
    fun ys =>
      match boundedSentential? (g := g) B ys with
      | some bw => bw
      | none => []
  have hfinite :=
    (boundedSententialForms_finite g L K).image encodeForm
  apply hfinite.subset
  intro bw hbw
  rcases hbw with ⟨ys, hys, henc⟩
  exact ⟨ys, hys, by simp [encodeForm, henc]⟩

/-- The part of the bounded full-context frontier reachable in at most `N` counted steps in
the fixed bounded-stack grammar is finite. -/
theorem finite_stepReachable_boundedSentential_image_of_boundedSententialForms_at_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {K B L N : ℕ} :
    ({bw : List (symbol T (BoundedStackNT g B)) |
      (∃ ys : List g.ISym,
        ys ∈ boundedSententialForms g L K ∧
          boundedSentential? (g := g) B ys = some bw) ∧
        ∃ p : ℕ, p ≤ N ∧
          grammar_derivesIn (boundedStackGrammar g B) p
            [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
        Set (List (symbol T (BoundedStackNT g B)))).Finite := by
  exact
    finite_boundedSentential_image_of_boundedSententialForms_at_bound
      (g := g) (K := K) (B := B) (L := L) |>.subset
        (by
          intro bw hbw
          exact hbw.1)

/-- Membership helper for the full bounded-sentential encoding frontier. -/
theorem boundedSentential_mem_boundedSentential_image_of_length_stackBound
    {g : IndexedGrammar T} {K B L : ℕ}
    {ys : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hlen : ys.length ≤ L)
    (hstack : sententialMaxStackHeight ys ≤ K)
    (hbw : boundedSentential? (g := g) B ys = some bw) :
    bw ∈
      ({bw : List (symbol T (BoundedStackNT g B)) |
        ∃ ys : List g.ISym,
          ys ∈ boundedSententialForms g L K ∧
            boundedSentential? (g := g) B ys = some bw} :
        Set (List (symbol T (BoundedStackNT g B)))) :=
  ⟨ys, ⟨hlen, hstack⟩, hbw⟩

/-- If a replacement context has a bounded `P`-surface of length at most `L` and it encodes
successfully at stack bound `B`, then its encoding belongs to the full bounded-sentential
frontier at bound `B`. -/
theorem boundedSentential_mem_boundedSentential_image_of_boundedSurface_boundedSentential?
    {g : IndexedGrammar T} {P B L : ℕ}
    {ys : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hsurface : surfaceOfTruncatedForm P ys ∈ boundedSurfaceForms g L P)
    (hbw : boundedSentential? (g := g) B ys = some bw) :
    bw ∈
      ({bw : List (symbol T (BoundedStackNT g B)) |
        ∃ ys : List g.ISym,
          ys ∈ boundedSententialForms g L B ∧
            boundedSentential? (g := g) B ys = some bw} :
        Set (List (symbol T (BoundedStackNT g B)))) := by
  have hlen : ys.length ≤ L := by
    have hsurfaceLen : (surfaceOfTruncatedForm P ys).length ≤ L := by
      simpa [boundedSurfaceForms] using hsurface
    simpa using hsurfaceLen
  exact
    boundedSentential_mem_boundedSentential_image_of_length_stackBound
      (g := g) (K := B) (B := B) (L := L) hlen
      (sententialMaxStackHeight_le_of_boundedSentential? hbw) hbw

/-- Constructor for the finite step-reachable full-context frontier from the concrete data
usually available in the late-window argument: a bounded visible surface, a successful bounded
encoding, and a counted compiled prefix path. -/
theorem stepReachable_boundedSentential_image_mem_of_boundedSurface_boundedSentential?_derivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {P B L N : ℕ}
    {ys : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hsurface : surfaceOfTruncatedForm P ys ∈ boundedSurfaceForms g L P)
    (hbw : boundedSentential? (g := g) B ys = some bw)
    (hreach : ∃ p : ℕ, p ≤ N ∧
      grammar_derivesIn (boundedStackGrammar g B) p
        [symbol.nonterminal (boundedStackGrammar g B).initial] bw) :
    bw ∈
      ({bw : List (symbol T (BoundedStackNT g B)) |
        (∃ ys : List g.ISym,
          ys ∈ boundedSententialForms g L B ∧
            boundedSentential? (g := g) B ys = some bw) ∧
          ∃ p : ℕ, p ≤ N ∧
            grammar_derivesIn (boundedStackGrammar g B) p
              [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
        Set (List (symbol T (BoundedStackNT g B)))) :=
  ⟨boundedSentential_mem_boundedSentential_image_of_boundedSurface_boundedSentential?
    (g := g) hsurface hbw, hreach⟩

/-- A stack-bounded indexed prefix witness gives membership in the finite step-reachable
full-context frontier for any successful bounded encoding of the reached sentential form. -/
theorem stepReachable_boundedSentential_image_mem_of_stackBoundedDerivesIn
    {g : IndexedGrammar T} [Fintype g.flag] {P B L N p : ℕ}
    {ys : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hsurface : surfaceOfTruncatedForm P ys ∈ boundedSurfaceForms g L P)
    (hbw : boundedSentential? (g := g) B ys = some bw)
    (hp : p ≤ N)
    (hpre : StackBoundedDerivesIn g B p [ISym.indexed g.initial []] ys) :
    bw ∈
      ({bw : List (symbol T (BoundedStackNT g B)) |
        (∃ ys : List g.ISym,
          ys ∈ boundedSententialForms g L B ∧
            boundedSentential? (g := g) B ys = some bw) ∧
          ∃ p : ℕ, p ≤ N ∧
            grammar_derivesIn (boundedStackGrammar g B) p
              [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
        Set (List (symbol T (BoundedStackNT g B)))) := by
  have hstart :
      boundedSentential? (g := g) B [ISym.indexed g.initial []] =
        some [symbol.nonterminal (boundedStackGrammar g B).initial] := by
    simp [boundedStackGrammar, boundedSentential?, boundedSymbol?]
  have hder :
      grammar_derivesIn (boundedStackGrammar g B) p
        [symbol.nonterminal (boundedStackGrammar g B).initial] bw :=
    boundedStackGrammar_derivesIn_of_stackBoundedDerivesIn_of_boundedSentential
      (g := g) (B := B) hstart hbw hpre
  exact
    stepReachable_boundedSentential_image_mem_of_boundedSurface_boundedSentential?_derivesIn
      (g := g) hsurface hbw ⟨p, hp, hder⟩

/-- Surface-repeat bridge into the finite step-reachable full-context frontier for an arbitrary
replacement sentential form.

If `ys` has the same `B`-surface as a prefix node whose whole prefix is already `B`-bounded,
and `ys` itself fits in `B`, then the bounded-stack encoding of `ys` is a member of the finite
counted frontier reachable within the advertised prefix budget. -/
theorem exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le
    {g : IndexedGrammar T} [Fintype g.flag]
    {P B L N : ℕ} {trace : List (List g.ISym)} {ys : List g.ISym}
    {i j : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length) (hij : i ≤ j) (hjN : j ≤ N)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hysStack : sententialMaxStackHeight ys ≤ B)
    (hsurfaceEq :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B ys)
    (hsurfaceBound : surfaceOfTruncatedForm P ys ∈ boundedSurfaceForms g L P) :
    ∃ bw : List (symbol T (BoundedStackNT g B)),
      boundedSentential? (g := g) B ys = some bw ∧
        bw ∈
          ({bw : List (symbol T (BoundedStackNT g B)) |
            (∃ ys : List g.ISym,
              ys ∈ boundedSententialForms g L B ∧
                boundedSentential? (g := g) B ys = some bw) ∧
              ∃ p : ℕ, p ≤ N ∧
                grammar_derivesIn (boundedStackGrammar g B) p
                  [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
            Set (List (symbol T (BoundedStackNT g B)))) := by
  obtain ⟨bw, hbw⟩ :=
    exists_boundedSentential?_of_sententialMaxStackHeight_le
      (g := g) (B := B) hysStack
  obtain ⟨p, hpj, hpre⟩ :=
    exists_stackBoundedDerivesIn_of_surface_eq_prefix_bound_le
      (g := g) (B := B) (trace := trace) (first := [ISym.indexed g.initial []])
      (ys := ys) htrace hhead hi hij hprefixBound hysStack hsurfaceEq
  refine ⟨bw, hbw, ?_⟩
  exact
    stepReachable_boundedSentential_image_mem_of_stackBoundedDerivesIn
      (g := g) (P := P) (B := B) (L := L) (N := N) (p := p)
      (ys := ys) (bw := bw) hsurfaceBound hbw (le_trans hpj hjN) hpre

/-- Late-window form of
`exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le` for an
arbitrary replacement stack.

The local late-window stack-growth bound supplies the bounded prefix path. The replacement stack
only has to fit in `B` and agree with the actual stack on the visible `B` prefix, so this bridge
can be used with prefix-preserving certificate shrinkers as well as the canonical suffix
shrinker. -/
theorem exists_stepReachable_boundedSentential_image_of_late_window_context_take_eq
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P B L N C a i j : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η ζ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hij : i ≤ j) (hjN : j ≤ N)
    (hζ : ζ.length ≤ B)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (htake : η.take B = ζ.take B)
    (hsurfaceBound :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
        boundedSurfaceForms g L P) :
    ∃ bw : List (symbol T (BoundedStackNT g B)),
      boundedSentential? (g := g) B (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
        bw ∈
          ({bw : List (symbol T (BoundedStackNT g B)) |
            (∃ ys : List g.ISym,
              ys ∈ boundedSententialForms g L B ∧
                boundedSentential? (g := g) B ys = some bw) ∧
              ∃ p : ℕ, p ≤ N ∧
                grammar_derivesIn (boundedStackGrammar g B) p
                  [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
            Set (List (symbol T (BoundedStackNT g B)))) := by
  let ys : List g.ISym := u ++ [ISym.indexed A ζ] ++ v
  obtain ⟨p, hpi, hpre⟩ :=
    exists_stackBoundedDerivesIn_late_window_context_take_eq
      (g := g) hNF htrace hhead hi hic hwindowBound hbefore hij hζ hctx htake
  have hysStack : sententialMaxStackHeight ys ≤ B := by
    simpa [ys] using hpre.final_maxStackHeight_le
  obtain ⟨bw, hbw⟩ :=
    exists_boundedSentential?_of_sententialMaxStackHeight_le
      (g := g) (B := B) hysStack
  refine ⟨bw, hbw, ?_⟩
  exact
    stepReachable_boundedSentential_image_mem_of_stackBoundedDerivesIn
      (g := g) (P := P) (B := B) (L := L) (N := N) (p := p)
      (ys := ys) (bw := bw) (by simpa [ys] using hsurfaceBound)
      hbw (le_trans hpi hjN) hpre

/-- Canonical late-window finite-frontier bridge phrased by suffix-prefix preservation.

This specializes `exists_stepReachable_boundedSentential_image_of_late_window_context_take_eq`
to the stack `η.take P ++ τ`. The replacement only needs to preserve the visible suffix prefix
below `P`; the theorem packages the resulting full `B`-surface agreement and bounded encoding. -/
theorem exists_stepReachable_boundedSentential_image_of_late_window_canonical_suffix_take_eq
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P K B L N C a i j : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length)
    (hic : i ≤ a + C)
    (hwindowBound : P + C + 1 ≤ B)
    (hbefore : ∀ k (hk : k < trace.length),
      k < a → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P)
    (hij : i ≤ j) (hjN : j ≤ N)
    (hPK : P + K ≤ B)
    (hτ : τ.length ≤ K)
    (hPη : P ≤ η.length)
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v)
    (hsuffix : τ.take (B - P) = (η.drop P).take (B - P))
    (hsurfaceBound :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
        boundedSurfaceForms g L P) :
    ∃ bw : List (symbol T (BoundedStackNT g B)),
      boundedSentential? (g := g) B
          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) = some bw ∧
        bw ∈
          ({bw : List (symbol T (BoundedStackNT g B)) |
            (∃ ys : List g.ISym,
              ys ∈ boundedSententialForms g L B ∧
                boundedSentential? (g := g) B ys = some bw) ∧
              ∃ p : ℕ, p ≤ N ∧
                grammar_derivesIn (boundedStackGrammar g B) p
                  [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
            Set (List (symbol T (BoundedStackNT g B)))) := by
  have hζ : (η.take P ++ τ).length ≤ B := by
    rw [List.length_append]
    have htake : (η.take P).length ≤ P := List.length_take_le P η
    omega
  have hPB : P ≤ B := le_trans (Nat.le_add_right P K) hPK
  have htake :
      η.take B = (η.take P ++ τ).take B :=
    (stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm
  exact
    exists_stepReachable_boundedSentential_image_of_late_window_context_take_eq
      (g := g) hNF htrace hhead hi hic hwindowBound hbefore hij hjN hζ hctx htake
      hsurfaceBound

/-- Surface-repeat bridge into the finite step-reachable full-context frontier.

If a canonical replacement context has the same `B`-surface as a prefix node whose whole prefix
is already `B`-bounded, and the replacement context itself fits in `B`, then its bounded-stack
encoding is a member of the finite counted frontier reachable within the advertised prefix
budget. -/
theorem exists_stepReachable_boundedSentential_image_of_canonical_context_surface_eq_prefix_bound_le
    {g : IndexedGrammar T} [Fintype g.flag]
    {P K B L N : ℕ} {trace : List (List g.ISym)}
    {u v : List g.ISym} {A : g.nt} {η τ : List g.flag}
    {i j : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hi : i < trace.length) (hij : i ≤ j) (hjN : j ≤ N)
    (hprefixBound : ∀ k (hk : k < trace.length),
      k ≤ i → sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ B)
    (hctx : sententialMaxStackHeight (u ++ v) ≤ B)
    (hPK : P + K ≤ B)
    (hτ : τ.length ≤ K)
    (hsurfaceEq :
      surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) =
        surfaceOfTruncatedForm B (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v))
    (hsurfaceBound :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
        boundedSurfaceForms g L P) :
    ∃ bw : List (symbol T (BoundedStackNT g B)),
      boundedSentential? (g := g) B
          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) = some bw ∧
        bw ∈
          ({bw : List (symbol T (BoundedStackNT g B)) |
            (∃ ys : List g.ISym,
              ys ∈ boundedSententialForms g L B ∧
                boundedSentential? (g := g) B ys = some bw) ∧
              ∃ p : ℕ, p ≤ N ∧
                grammar_derivesIn (boundedStackGrammar g B) p
                  [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
            Set (List (symbol T (BoundedStackNT g B)))) := by
  let ys : List g.ISym := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v
  have hysStack : sententialMaxStackHeight ys ≤ B := by
    simpa [ys] using
      sententialMaxStackHeight_context_indexed_take_append_le
        (g := g) (u := u) (v := v) (A := A) (η := η) (τ := τ)
        (P := P) (K := K) (B := B) hctx hPK hτ
  exact
    exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le
      (g := g) (P := P) (B := B) (L := L) (N := N) (trace := trace)
      (ys := ys) (i := i) (j := j)
      htrace hhead hi hij hjN hprefixBound hysStack
      (by simpa [ys] using hsurfaceEq)
      (by simpa [ys] using hsurfaceBound)

/-- A counted reachable member of the finite full-context bounded-sentential frontier gives
the exact stack-bounded indexed prefix witness for the corresponding decoded sentential
form. -/
theorem exists_stackBoundedDerivesIn_le_of_stepReachable_boundedSentential_image
    {g : IndexedGrammar T} [Fintype g.flag] {K B L N : ℕ}
    {ys : List g.ISym} {bw : List (symbol T (BoundedStackNT g B))}
    (hbw : boundedSentential? (g := g) B ys = some bw)
    (hfrontier :
      bw ∈
        ({bw : List (symbol T (BoundedStackNT g B)) |
          (∃ ys : List g.ISym,
            ys ∈ boundedSententialForms g L K ∧
              boundedSentential? (g := g) B ys = some bw) ∧
            ∃ p : ℕ, p ≤ N ∧
              grammar_derivesIn (boundedStackGrammar g B) p
                [symbol.nonterminal (boundedStackGrammar g B).initial] bw} :
          Set (List (symbol T (BoundedStackNT g B))))) :
    ∃ p : ℕ, p ≤ N ∧
      StackBoundedDerivesIn g B p [ISym.indexed g.initial []] ys := by
  exact
    exists_stackBoundedDerivesIn_le_of_boundedStackGrammar_derivesIn_initial_boundedSentential
      (g := g) (B := B) (i := N) hbw hfrontier.2

/-- Finite-frontier version of the whole-surface replacement bridge.

The suffix shrinker only needs each target-compatible finite surface to be reachable by some
bounded prefix no longer than the current trace prefix. This reformulation packages that
reachability as membership in the counted, finite, full-sentential frontier of the fixed
bounded-stack grammar. -/
theorem
    exists_bound_minimal_stackBound_le_max_of_stepReachable_targetCompatible_surface_suffix_replacement_budget
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
                ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                  boundedSentential? (g := g) Bpre (eraseSurfaceForm surface) = some bw ∧
                    bw ∈
                      ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                        (∃ ys : List g.ISym,
                          ys ∈ boundedSententialForms g L Bpre ∧
                            boundedSentential? (g := g) Bpre ys = some bw) ∧
                          ∃ p : ℕ, p ≤ i ∧
                            grammar_derivesIn (boundedStackGrammar g Bpre) p
                              [symbol.nonterminal
                                (boundedStackGrammar g Bpre).initial] bw} :
                        Set (List (symbol T (BoundedStackNT g Bpre))))) →
              B ≤ max Bpre (K + N) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_max_of_shorter_reachable_targetCompatible_surface_suffix_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen n B trace htrace hlen hlast hminLength hminBound
    i hi Bpre hsuffixBudget hreachable
  exact
    hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
      i hi Bpre hsuffixBudget
      (by
        intro surface hsurface
        obtain ⟨bw, hbw, hfrontier⟩ := hreachable surface hsurface
        exact
          exists_stackBoundedDerivesIn_le_of_stepReachable_boundedSentential_image
            (g := g) (K := Bpre) (B := Bpre) (L := L) (N := i)
            (ys := eraseSurfaceForm surface) (bw := bw) hbw hfrontier)

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

/-- Target-compatible finite-frontier acceptance bridge.

The suffix shrinker produces a start form `bw` in the finite target-compatible surface
frontier and a fixed bounded-stack suffix derivation `bw ⇒* target`. If the finite frontier
has been saturated enough to prove that every such suffix start is reachable from the bounded
grammar's initial symbol, then the target belongs to that same fixed bounded-stack grammar. -/
theorem exists_bound_boundedStackGrammar_generates_of_reachable_targetCompatible_suffix_frontier_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ _hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            (∀ bw : List (symbol T (BoundedStackNT g (K + N))),
              bw ∈
                ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                  ∃ surface : SurfaceForm g K,
                    surface ∈ targetCompatibleBoundedSurfaceForms g target K ∧
                      boundedSentential? (g := g) (K + N)
                        (eraseSurfaceForm surface) = some bw} :
                  Set (List (symbol T (BoundedStackNT g (K + N)))) ) →
              grammar_derives (boundedStackGrammar g (K + N)) bw
                (target.map fun a =>
                  (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) →
              grammar_derives (boundedStackGrammar g (K + N))
                [symbol.nonterminal (boundedStackGrammar g (K + N)).initial] bw) →
            target ∈ grammar_language (boundedStackGrammar g (K + N)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget hreachable
  obtain ⟨ys, n', bw, _hn', _hrel, _hlenEq, _htermEq, _hntEq, _hysBound,
    _hsurface, _herase, _hbw, hbwm, hGder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  exact boundedStackGrammar_generates_of_prefix_suffix_derives
    (g := g) (B := K + N)
    (hreachable bw hbwm hGder) hGder

/-- Length-uniform finite-frontier acceptance bridge.

This is the target-independent frontier version of
`exists_bound_boundedStackGrammar_generates_of_reachable_targetCompatible_suffix_frontier_budget`:
the suffix start is required only to lie in the finite set of visible surfaces of length at
most `L`. -/
theorem exists_bound_boundedStackGrammar_generates_of_reachable_suffix_frontier_lengthBound_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          IsDerivationTrace g trace →
          trace.getLast? = some (target.map fun a => (ISym.terminal a : g.ISym)) →
          ∀ i : ℕ, ∀ _hi : i < trace.length,
            trace.length - 1 - i ≤ N →
            (∀ bw : List (symbol T (BoundedStackNT g (K + N))),
              bw ∈
                ({bw : List (symbol T (BoundedStackNT g (K + N))) |
                  ∃ surface : SurfaceForm g K,
                    surface ∈ boundedSurfaceForms g L K ∧
                      boundedSentential? (g := g) (K + N)
                        (eraseSurfaceForm surface) = some bw} :
                  Set (List (symbol T (BoundedStackNT g (K + N)))) ) →
              grammar_derives (boundedStackGrammar g (K + N)) bw
                (target.map fun a =>
                  (symbol.terminal a : symbol T (BoundedStackNT g (K + N)))) →
              grammar_derives (boundedStackGrammar g (K + N))
                [symbol.nonterminal (boundedStackGrammar g (K + N)).initial] bw) →
            target ∈ grammar_language (boundedStackGrammar g (K + N)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_suffix_derives_of_accepting_derivationTrace_symbols_suffix_shrink_surface_lengthBound_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen trace htrace hlast i hi hsuffixBudget hreachable
  obtain ⟨ys, n', bw, _hn', _hrel, _hlenEq, _htermEq, _hntEq, _hysBound,
    _hsurface, _herase, _hbw, hbwm, hGder⟩ :=
    hK target htargetLen trace htrace hlast i hi hsuffixBudget
  exact boundedStackGrammar_generates_of_prefix_suffix_derives
    (g := g) (B := K + N)
    (hreachable bw hbwm hGder) hGder

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

theorem boundedStackGrammar_language_iff_stackBounded_certificate
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {B : ℕ} {w : List T} :
    w ∈ grammar_language (boundedStackGrammar g B) ↔
      NFYield.StackBounded g B g.initial [] w := by
  constructor
  · intro hw
    rcases (boundedStackGrammar_language_iff_exists_stackBoundedDerivesIn
        (g := g) (B := B) (w := w)).mp hw with
      ⟨n, hbounded⟩
    exact NFYield.StackBounded.of_stackBoundedDerivesIn_isNormalForm_exact
      (g := g) hNF hbounded
  · intro hcert
    exact boundedStackGrammar_generates_of_stackBounded_certificate (g := g) hcert

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

/-- Flat finite-path certificate extracted from a generated word of a fixed bounded-stack
slice. This is the bridge from the finite noncontracting slice back to the flat indexed
sentential-form search space used by the eventual LBA simulation. -/
theorem exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B L : ℕ} {w : List T} (hwlen : w.length ≤ L)
    (hw : w ∈ grammar_language (boundedStackGrammar g B)) :
    ∃ n : ℕ,
    ∃ trace : List (List g.ISym),
    ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
      IsDerivationTrace g trace ∧
      ftrace = flatTrace trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      ftrace.length = n + 1 ∧
      (∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
      ftrace.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      ftrace.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin ftrace.length,
        ftrace.get i ∈ boundedFlatForms g (L * (B + 2))) ∧
      (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
        FlatTransforms g
          (ftrace.get ⟨i, by omega⟩)
          (ftrace.get ⟨i + 1, hi⟩)) ∧
      FlatDerives g
        (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) := by
  obtain ⟨n, hbounded⟩ :=
    (boundedStackGrammar_language_iff_exists_stackBoundedDerivesIn
      (g := g) (B := B) (w := w)).mp hw
  obtain ⟨trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives⟩ :=
    exists_bounded_accepting_flatTrace_of_stackBoundedDerivesIn_isNormalForm
      (g := g) hNF (B := B) (L := L) hwlen hbounded
  exact ⟨n, trace, ftrace, htrace, hftrace, hlen, hhead, hlast, hflen, hstack,
    hfhead, hflast, hfbound, hfstep, hfderives⟩

/-- Fixed-slice bridge from the bounded-stack grammar to the bounded flat-path language. -/
theorem boundedFlatPathLanguage_of_boundedStackGrammar_language_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B L : ℕ} {w : List T} (hwlen : w.length ≤ L)
    (hw : w ∈ grammar_language (boundedStackGrammar g B)) :
    w ∈ boundedFlatPathLanguage g (L * (B + 2)) := by
  obtain ⟨_n, _trace, ftrace, _htrace, _hftrace, _hlen, _hhead, _hlast, _hflen,
    _hstack, hfhead, hflast, hfbound, hfstep, _hfderives⟩ :=
    exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := B) (L := L) hwlen hw
  exact ⟨ftrace, hfhead, hflast, hfbound, hfstep⟩

/-- Exact-length form of
`exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_isNormalForm`.

This packages the bounded-stack-to-flat-path bridge with the flat tape bound computed from the
actual input length, which is the shape needed by the eventual input-parametric LBA
simulation. -/
theorem exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_length_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B : ℕ} {w : List T}
    (hw : w ∈ grammar_language (boundedStackGrammar g B)) :
    ∃ n : ℕ,
    ∃ trace : List (List g.ISym),
    ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
      IsDerivationTrace g trace ∧
      ftrace = flatTrace trace ∧
      trace.length = n + 1 ∧
      trace.head? = some [ISym.indexed g.initial []] ∧
      trace.getLast? = some (w.map fun a => (ISym.terminal a : g.ISym)) ∧
      ftrace.length = n + 1 ∧
      (∀ i (hi : i < trace.length),
        sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
      ftrace.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      ftrace.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin ftrace.length,
        ftrace.get i ∈ boundedFlatForms g (w.length * (B + 2))) ∧
      (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
        FlatTransforms g
          (ftrace.get ⟨i, by omega⟩)
          (ftrace.get ⟨i + 1, hi⟩)) ∧
      FlatDerives g
        (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) := by
  exact
    exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := B) (L := w.length) (w := w) le_rfl hw

/-- Exact-length fixed-slice bridge from the bounded-stack grammar to the bounded flat-path
language. -/
theorem boundedFlatPathLanguage_of_boundedStackGrammar_language_length_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B : ℕ} {w : List T}
    (hw : w ∈ grammar_language (boundedStackGrammar g B)) :
    w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) := by
  exact
    boundedFlatPathLanguage_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := B) (L := w.length) (w := w) le_rfl hw

/-- Per-word exact flat-bound characterization of normal-form generation.

The remaining finite normal-form core has to make the stack bound uniform enough for one LBA;
this theorem isolates the already-proved part: once a stack bound exists for the word, the flat
certificate uses only `|w| * (B + 2)` cells. -/
theorem language_iff_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w : List T} :
    w ∈ g.Language ↔
      ∃ B : ℕ, w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) := by
  constructor
  · intro hgen
    have hcert : NFYield g g.initial [] w :=
      (NFYield.generates_iff_isNormalForm (g := g) hNF).mp hgen
    obtain ⟨B, hB⟩ :=
      (exists_boundedStackGrammar_generates_iff_certificate (g := g) hNF (w := w)).mpr
        hcert
    exact ⟨B, boundedFlatPathLanguage_of_boundedStackGrammar_language_length_isNormalForm
      (g := g) hNF hB⟩
  · rintro ⟨B, hflat⟩
    exact boundedFlatPathLanguage_subset_language
      (g := g) (B := w.length * (B + 2)) hflat

/-- Per-word exact packed-reachability characterization of nonempty normal-form generation.

This is the packed-tape form of
`language_iff_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm`: the flat
certificate of width `B + 2` per input symbol is represented over exactly `|w|` tape cells. -/
theorem language_iff_exists_packedFlatDerives_width_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w : List T} (hwne : w ≠ []) :
    w ∈ g.Language ↔
      ∃ B : ℕ,
        PackedFlatDerives g (B + 2) w.length
          (packedBoundedFlatForm g (B + 2) w.length
            ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
              initial_mem_boundedFlatForms_length_mul_of_pos
                (g := g) (B := B) (w := w) (List.length_pos_of_ne_nil hwne)⟩)
          (packedBoundedFlatForm g (B + 2) w.length
            ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
              terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩) := by
  rw [language_iff_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm
    (g := g) hNF]
  constructor
  · rintro ⟨B, hflat⟩
    exact ⟨B,
      (boundedFlatPathLanguage_length_iff_packedFlatDerives
        (g := g) (B := B) (w := w) hwne).mp hflat⟩
  · rintro ⟨B, hpacked⟩
    exact ⟨B,
      (boundedFlatPathLanguage_length_iff_packedFlatDerives
        (g := g) (B := B) (w := w) hwne).mpr hpacked⟩

/-- Packed-language form of normal-form generation.

A finite normal-form grammar generates exactly the union, over all stack bounds `B`, of the
fixed-stack-bound packed flat-path languages. This packages the nonempty side condition inside
the packed language itself, so the statement is a genuine language equality rather than a
relation with a separate endpoint well-formedness proof. -/
theorem language_iff_exists_packedFlatPathStackBoundLanguage_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w : List T} :
    w ∈ g.Language ↔
      ∃ B : ℕ, w ∈ packedFlatPathStackBoundLanguage g B := by
  constructor
  · intro hgen
    have hwne : w ≠ [] := by
      intro hw
      subst w
      exact (g.not_generates_nil_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF)) hgen
    obtain ⟨B, hpacked⟩ :=
      (language_iff_exists_packedFlatDerives_width_isNormalForm
        (g := g) hNF (w := w) hwne).mp hgen
    exact ⟨B, hwne, hpacked⟩
  · rintro ⟨B, hpacked⟩
    exact packedFlatPathStackBoundLanguage_subset_language
      (g := g) (B := B) hpacked

/-- Set-level form of
`language_iff_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm`. -/
theorem language_eq_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm) :
    g.Language =
      fun w : List T => ∃ B : ℕ, w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) := by
  ext w
  exact language_iff_exists_boundedFlatPathLanguage_length_stackBound_isNormalForm
    (g := g) hNF

/-- Set-level form of
`language_iff_exists_packedFlatPathStackBoundLanguage_isNormalForm`. -/
theorem language_eq_exists_packedFlatPathStackBoundLanguage_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt] (hNF : g.IsNormalForm) :
    g.Language =
      fun w : List T => ∃ B : ℕ, w ∈ packedFlatPathStackBoundLanguage g B := by
  ext w
  exact language_iff_exists_packedFlatPathStackBoundLanguage_isNormalForm
    (g := g) hNF

/-- A bounded flat path decodes to a counted indexed derivation whose intermediate stack
heights are bounded by the same flat tape bound. -/
theorem exists_stackBoundedDerivesIn_of_boundedFlatPath
    {g : IndexedGrammar T} {B : ℕ} {w₁ w₂ : List g.ISym}
    {path : List (List (FlatSymbol T g.nt g.flag))}
    (hhead : path.head? = some (encodeSentential w₁))
    (hlast : path.getLast? = some (encodeSentential w₂))
    (hbound : ∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B)
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < path.length,
      FlatTransforms g
        (path.get ⟨i, by omega⟩)
        (path.get ⟨i + 1, hi⟩)) :
    ∃ n : ℕ, StackBoundedDerivesIn g B n w₁ w₂ := by
  induction path generalizing w₁ w₂ with
  | nil =>
      simp at hhead
  | cons x rest ih =>
      cases rest with
      | nil =>
          have hx₁ : x = encodeSentential w₁ := by
            simpa using hhead
          have hx₂ : x = encodeSentential w₂ := by
            simpa using hlast
          have hw : w₁ = w₂ := by
            exact encodeSentential_injective (by rw [← hx₁, ← hx₂])
          subst w₂
          have hxBound : x.length ≤ B := by
            simpa [boundedFlatForms] using
              hbound ⟨0, by simp⟩
          have hwBound : sententialMaxStackHeight w₁ ≤ B := by
            exact le_trans (sententialMaxStackHeight_le_encodeSentential_length w₁)
              (by simpa [← hx₁] using hxBound)
          exact ⟨0, rfl, hwBound⟩
      | cons y rest =>
          have hx₁ : x = encodeSentential w₁ := by
            simpa using hhead
          rcases hstep 0 (by simp) with ⟨u, v, hxDec, hyDec, hxy⟩
          have hu : u = w₁ := by
            apply Option.some.inj
            rw [← hxDec, hx₁]
            simp
          subst u
          have hyEnc : y = encodeSentential v :=
            decodeFlatSentential_eq_some_iff.mp hyDec
          have hheadTail : (y :: rest).head? = some (encodeSentential v) := by
            simp [hyEnc]
          have hlastTail : (y :: rest).getLast? = some (encodeSentential w₂) := by
            simpa using hlast
          have hboundTail :
              ∀ i : Fin (y :: rest).length,
                (y :: rest).get i ∈ boundedFlatForms g B := by
            intro i
            have hiOrig : i.1 + 1 < (x :: y :: rest).length := by
              simpa using Nat.succ_lt_succ i.2
            simpa using hbound ⟨i.1 + 1, hiOrig⟩
          have hstepTail :
              ∀ i : ℕ, ∀ hi : i + 1 < (y :: rest).length,
                FlatTransforms g
                  ((y :: rest).get ⟨i, by omega⟩)
                  ((y :: rest).get ⟨i + 1, hi⟩) := by
            intro i hi
            have hiOrig : (i + 1) + 1 < (x :: y :: rest).length := by
              simpa using Nat.succ_lt_succ hi
            simpa using hstep (i + 1) hiOrig
          obtain ⟨n, htail⟩ :=
            ih hheadTail hlastTail hboundTail hstepTail
          have hxBound : x.length ≤ B := by
            simpa [boundedFlatForms] using
              hbound ⟨0, by simp⟩
          have hw₁Bound : sententialMaxStackHeight w₁ ≤ B := by
            exact le_trans (sententialMaxStackHeight_le_encodeSentential_length w₁)
              (by simpa [← hx₁] using hxBound)
          have hyBound : y.length ≤ B := by
            simpa [boundedFlatForms] using
              hbound ⟨1, by simp⟩
          have hvBound : sententialMaxStackHeight v ≤ B := by
            exact le_trans (sententialMaxStackHeight_le_of_decodeFlatSentential_eq_some hyDec)
              hyBound
          have hone : StackBoundedDerivesIn g B 1 w₁ v :=
            stackBoundedDerivesIn_one_of_transforms hxy hw₁Bound hvBound
          exact ⟨1 + n, stackBoundedDerivesIn_trans hone htail⟩

/-- Fixed-slice reverse bridge: any accepted bounded flat path is generated by the corresponding
bounded-stack grammar with the same stack bound. -/
theorem boundedStackGrammar_language_of_boundedFlatPathLanguage
    {g : IndexedGrammar T} [Fintype g.flag] {B : ℕ} {w : List T}
    (hw : w ∈ boundedFlatPathLanguage g B) :
    w ∈ grammar_language (boundedStackGrammar g B) := by
  rcases hw with ⟨path, hhead, hlast, hbound, hstep⟩
  have hlast' :
      path.getLast? =
        some (encodeSentential (w.map fun a => (ISym.terminal a : g.ISym))) := by
    simpa using hlast
  obtain ⟨n, hbounded⟩ :=
    exists_stackBoundedDerivesIn_of_boundedFlatPath
      (g := g) (B := B)
      (w₁ := [ISym.indexed g.initial []])
      (w₂ := w.map fun a => (ISym.terminal a : g.ISym))
      hhead hlast' hbound hstep
  exact boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded

/-- Normal-form certificate form of the fixed-slice reverse bridge. -/
theorem stackBounded_certificate_of_boundedFlatPathLanguage_isNormalForm
    {g : IndexedGrammar T} [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {B : ℕ} {w : List T}
    (hw : w ∈ boundedFlatPathLanguage g B) :
    NFYield.StackBounded g B g.initial [] w := by
  exact (boundedStackGrammar_language_iff_stackBounded_certificate
    (g := g) hNF (B := B) (w := w)).mp
    (boundedStackGrammar_language_of_boundedFlatPathLanguage (g := g) hw)

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

/-- Generated-word wrapper for the finite-frontier whole-surface bridge.

For a fixed suffix budget `N`, choose a shortest accepting trace and then a least stack bound
among traces of that length. If the trace has fewer than `N` steps, the step-count bound
already compiles it into the final bounded-stack grammar. Otherwise, cutting exactly `N`
steps from the end reduces the remaining obligation to finite-frontier reachability of every
target-compatible replacement surface at that cut. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_stepReachable_targetCompatible_surface_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
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
              (N ≤ n →
                ∀ surface : SurfaceForm g K,
                  surface ∈ targetCompatibleBoundedSurfaceForms g target K →
                  ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                    boundedSentential? (g := g) Bpre (eraseSurfaceForm surface) =
                      some bw ∧
                      bw ∈
                        ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                          (∃ ys : List g.ISym,
                            ys ∈ boundedSententialForms g L Bpre ∧
                              boundedSentential? (g := g) Bpre ys = some bw) ∧
                            ∃ p : ℕ, p ≤ trace.length - 1 - N ∧
                              grammar_derivesIn (boundedStackGrammar g Bpre) p
                                [symbol.nonterminal
                                  (boundedStackGrammar g Bpre).initial] bw} :
                          Set (List (symbol T (BoundedStackNT g Bpre))))) →
              target ∈
                grammar_language (boundedStackGrammar g (max Bpre (K + N))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_minimal_stackBound_le_max_of_stepReachable_targetCompatible_surface_suffix_replacement_budget
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hreachable
  let Bfinal := max Bpre (K + N)
  by_cases hnN : N ≤ n
  · let i : ℕ := trace.length - 1 - N
    have hi : i < trace.length := by
      simp [i]
      omega
    have hsuffixBudget : trace.length - 1 - i ≤ N := by
      simp [i]
      omega
    have htraceBoundMem :
        ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
      intro x hx
      rcases List.mem_iff_get.mp hx with ⟨j, hj⟩
      rw [← hj]
      exact hbound j.1 j.2
    have hbounded :
        StackBoundedDerivesIn g B n [ISym.indexed g.initial []]
          (target.map fun a => (ISym.terminal a : g.ISym)) :=
      stackBoundedDerivesIn_of_bounded_isDerivationTrace
        (g := g) htrace hlen hhead hlast htraceBoundMem
    have htargetB : target ∈ grammar_language (boundedStackGrammar g B) :=
      boundedStackGrammar_generates_of_stackBoundedDerivesIn (g := g) hbounded
    have hBfinal : B ≤ Bfinal := by
      simpa [Bfinal] using
        hK target htargetLen n B trace htrace hlen hlast hminLength hminBound
          i hi Bpre hsuffixBudget
          (by
            intro surface hsurface
            exact hreachable hnN surface hsurface)
    exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) hBfinal target htargetB
  · have hnLt : n < N := Nat.lt_of_not_ge hnN
    have htargetN :
        target ∈ grammar_language (boundedStackGrammar g n) :=
      boundedStackGrammar_generates_of_derivesIn_isNormalForm
        (g := g) hNF hder
    exact boundedStackGrammar_language_mono
      (g := g) (B := n) (C := Bfinal) (by omega) target htargetN

/-- Flat-path form of
`exists_bound_boundedStackGrammar_generates_of_stepReachable_targetCompatible_surface_reachability`.

The prefix reachability premise is still the finite counted full-sentential frontier at the
chosen cut. The conclusion is now an explicit flat accepting path whose every node lies in a
finite flat space determined by the compiled bound `max Bpre (K + N)`. -/
theorem
    exists_bound_bounded_flatPath_of_stepReachable_targetCompatible_surface_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ) :
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
              (N ≤ n →
                ∀ surface : SurfaceForm g K,
                  surface ∈ targetCompatibleBoundedSurfaceForms g target K →
                  ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                    boundedSentential? (g := g) Bpre (eraseSurfaceForm surface) =
                      some bw ∧
                      bw ∈
                        ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                          (∃ ys : List g.ISym,
                            ys ∈ boundedSententialForms g L Bpre ∧
                              boundedSentential? (g := g) Bpre ys = some bw) ∧
                            ∃ p : ℕ, p ≤ trace.length - 1 - N ∧
                              grammar_derivesIn (boundedStackGrammar g Bpre) p
                                [symbol.nonterminal
                                  (boundedStackGrammar g Bpre).initial] bw} :
                          Set (List (symbol T (BoundedStackNT g Bpre))))) →
              ∃ m : ℕ,
              ∃ trace' : List (List g.ISym),
              ∃ ftrace : List (List (FlatSymbol T g.nt g.flag)),
                IsDerivationTrace g trace' ∧
                ftrace = flatTrace trace' ∧
                trace'.length = m + 1 ∧
                trace'.head? = some [ISym.indexed g.initial []] ∧
                trace'.getLast? =
                  some (target.map fun a => (ISym.terminal a : g.ISym)) ∧
                ftrace.length = m + 1 ∧
                (∀ i (hi : i < trace'.length),
                  sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ max Bpre (K + N)) ∧
                ftrace.head? =
                  some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
                ftrace.getLast? =
                  some (target.map fun a =>
                    (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
                (∀ i : Fin ftrace.length,
                  ftrace.get i ∈
                    boundedFlatForms g (L * ((max Bpre (K + N)) + 2))) ∧
                (∀ i : ℕ, ∀ hi : i + 1 < ftrace.length,
                  FlatTransforms g
                    (ftrace.get ⟨i, by omega⟩)
                    (ftrace.get ⟨i + 1, hi⟩)) ∧
                FlatDerives g
                  (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
                  (target.map fun a =>
                    (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_stepReachable_targetCompatible_surface_reachability
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hreachable
  exact
    exists_bounded_accepting_flatPath_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := max Bpre (K + N)) (L := L) htargetLen
      (hgenerated Bpre hreachable)

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

/-- Generated-word form of the prefix-preserving late-window replacement bridge.

For a generated target, choose a shortest accepting trace and then a least stack bound `B`
among traces of that length. The remaining reachability premise is phrased for the concrete
replacement stack `ζ` produced by the prefix-preserving shrinker, together with its sublist,
length, and visible-prefix facts. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A ζ] ++ v)) →
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
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_prefix_preserving_max_stack
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
          intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
            hζeq hζsub hζlen hζtake
          exact hreachable i hi
            (by simpa [Csurf] using hlow)
            (by simpa [Csurf] using hup)
            hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen hζeq hζsub
            hζlen hζtake)
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

/-- Bounded-grammar prefix form of the prefix-preserving late-window bridge.

Instead of asking directly for an indexed stack-bounded prefix derivation to the replacement
context, this wrapper asks for a bounded-stack grammar encoding of that context reachable in
at most the current prefix length. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_boundedGrammarDerivesIn_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
                        ∃ p : ℕ,
                          p ≤ i ∧
                            grammar_derivesIn (boundedStackGrammar g Bpre) p
                              [symbol.nonterminal (boundedStackGrammar g Bpre).initial]
                              bw) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
        hζeq hζsub hζlen hζtake
      obtain ⟨bw, hbw, p, hpi, hp⟩ :=
        hreachable i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub
          hτlen hζeq hζsub hζlen hζtake
      exact ⟨p, hpi,
        stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential
          (g := g) (B := Bpre) hbw hp⟩)

/-- Finite-step-frontier form of the prefix-preserving late-window bridge.

The remaining reachability premise is membership in the finite full-context bounded-sentential
frontier reachable in at most the current prefix length. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_stepReachableSentential_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
                        bw ∈
                          ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                            (∃ ys : List g.ISym,
                              ys ∈ boundedSententialForms g L Bpre ∧
                                boundedSentential? (g := g) Bpre ys = some bw) ∧
                              ∃ p : ℕ, p ≤ i ∧
                                grammar_derivesIn (boundedStackGrammar g Bpre) p
                                  [symbol.nonterminal
                                    (boundedStackGrammar g Bpre).initial] bw} :
                            Set (List (symbol T (BoundedStackNT g Bpre)))) ) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_boundedGrammarDerivesIn_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
        hζeq hζsub hζlen hζtake
      obtain ⟨bw, hbw, hfrontier⟩ :=
        hreachable i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub
          hτlen hζeq hζsub hζlen hζtake
      exact ⟨bw, hbw, hfrontier.2⟩)

/-- Frontier-facing generated-word form of the prefix-preserving late-window bridge.

This is the same fixed bounded-stack conclusion as
`exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_stepReachableSentential_reachability`,
but the remaining reachability premise receives the proof that the prefix-preserving
replacement context has a visible `P`-surface in both finite frontiers. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
                        bw ∈
                          ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                            (∃ ys : List g.ISym,
                              ys ∈ boundedSententialForms g L Bpre ∧
                                boundedSentential? (g := g) Bpre ys = some bw) ∧
                              ∃ p : ℕ, p ≤ i ∧
                                grammar_derivesIn (boundedStackGrammar g Bpre) p
                                  [symbol.nonterminal
                                    (boundedStackGrammar g Bpre).initial] bw} :
                            Set (List (symbol T (BoundedStackNT g Bpre)))) ) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_stepReachableSentential_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
        hζeq hζsub hζlen hζtake
      have htargetSurface :
          surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
            targetCompatibleBoundedSurfaceForms g target P :=
        surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms
          (g := g) (P := P) (target := target) (trace := trace)
          hNF htrace hlast hi (u := u) (v := v) (A := A) (η := η) (ζ := ζ)
          hctx hζtake
      have hboundedSurface :
          surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
            boundedSurfaceForms g L P :=
        surfaceOfTruncatedForm_prefix_preserving_context_mem_boundedSurfaceForms_lengthBound
          (g := g) (P := P) (L := L) (target := target) (trace := trace)
          hNF htrace hlast htargetLen hi
          (u := u) (v := v) (A := A) (η := η) (ζ := ζ) hctx hζtake
      exact hreachable i hi hlow hup hhigh A η τ ζ u v
        hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen hζtake
        htargetSurface hboundedSurface)

/-- Full-prefix form of the prefix-preserving late-window frontier bridge.

The finite step-reachable frontier premise is discharged locally from equality of the full
visible `Bpre` stack prefix. This is the generated-word lift of
`exists_stepReachable_boundedSentential_image_of_late_window_context_take_eq`. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_context_take_eq
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
              P + (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card + 1 ≤
                Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
                i ≤ trace.length - 1 -
                      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    η.take Bpre = ζ.take Bpre) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
        hζeq hζsub hζlen hζtake _htargetSurface hboundedSurface
      have htake :
          η.take Bpre = ζ.take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx
          hτsub hτlen hζeq hζsub hζlen hζtake
      have hζBound : ζ.length ≤ Bpre := le_trans hζlen hPK
      exact
        exists_stepReachable_boundedSentential_image_of_late_window_context_take_eq
          (g := g) hNF (P := P) (B := Bpre) (L := L) (N := i)
          (C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card)
          (a := trace.length - 1 -
            (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card)
          (i := i) (j := i) htrace hhead hi hup hwindowBound hbeforeBound
          le_rfl le_rfl hζBound hctx htake hboundedSurface)

/-- Full-surface-repeat form of the prefix-preserving late-window bridge.

The finite-step frontier premise in
`exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_reachability`
is discharged by a concrete earlier trace position whose full `Bpre`-surface matches the
replacement context. The replacement stack only has to preserve the first `P` flags and fit
under the advertised `P + K` budget. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_surfaceRepeat_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
                  ∀ u v : List g.ISym,
                    ISym.indexed A η ∈ trace.get ⟨i, hi⟩ →
                    η.length = sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                    trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A η] ++ v →
                    τ.Sublist (η.drop P) →
                    τ.length ≤ K →
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_prefix_preserving_frontier_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v hmem hηmax hctx hτsub hτlen
        hζeq hζsub hζlen hζtake htargetSurface hboundedSurface
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v
          hmem hηmax hctx hτsub hτlen hζeq hζsub hζlen hζtake
          htargetSurface hboundedSurface
      have hζBound : ζ.length ≤ Bpre := le_trans hζlen hPK
      have hysStack :
          sententialMaxStackHeight (u ++ [ISym.indexed A ζ] ++ v) ≤ Bpre :=
        sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le
          (g := g) (u := u) (v := v) (A := A) (σ := ζ)
          hctxBound hζBound
      exact
        exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le
          (g := g) (P := P) (B := Bpre) (L := L) (N := i)
          (trace := trace) (ys := u ++ [ISym.indexed A ζ] ++ v)
          (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound
          hysStack hsurfaceEq hboundedSurface)

/-- Generated-word form of the certified prefix-preserving late-window bridge.

For a generated target, choose a shortest accepting trace and then a least stack bound `B`
among traces of that length. The remaining reachability premise receives the concrete
prefix-preserving replacement stack, its local derivation certificate, and the accepting
replacement suffix produced by the shrinker. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A ζ] ++ v)) →
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
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_prefix_preserving_max_stack
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
          intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx
            hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake
            hζder hcert hreplacement hτmin
          exact hreachable i hi
            (by simpa [Csurf] using hlow)
            (by simpa [Csurf] using hup)
            hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen hq hm
            hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
            hreplacement hτmin)
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

/-- Frontier-facing generated-word form of the certified prefix-preserving late-window bridge.

This packages the concrete prefix-preserving replacement with the finite visible-surface
frontiers and the finite parse-certificate item frontiers. The reachability premise can
therefore reason only about bounded, finitely enumerable data. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ p : ℕ,
                      p ≤ i ∧
                        StackBoundedDerivesIn g Bpre p [ISym.indexed g.initial []]
                          (u ++ [ISym.indexed A ζ] ++ v)) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin
      have htargetSurface :
          surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
            targetCompatibleBoundedSurfaceForms g target P :=
        surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms
          (g := g) (P := P) (target := target) (trace := trace)
          hNF htrace hlast hi (u := u) (v := v) (A := A) (η := η) (ζ := ζ)
          hctx hζtake
      have hboundedSurface :
          surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
            boundedSurfaceForms g L P :=
        surfaceOfTruncatedForm_prefix_preserving_context_mem_boundedSurfaceForms_lengthBound
          (g := g) (P := P) (L := L) (target := target) (trace := trace)
          hNF htrace hlast htargetLen hi
          (u := u) (v := v) (A := A) (η := η) (ζ := ζ) hctx hζtake
      have hpref : (η.take P).length ≤ P := by
        exact List.length_take_le P η
      have hcertPref : NFYield g A (η.take P ++ τ) w := by
        simpa [hζeq] using hcert
      have htargetItem :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) := by
        have hitem :
            (((A, η.take P ++ τ), w) : (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) :=
          NFYield.bounded_prefix_certificate_mem_bounded_target_items
            (g := g) (N := P) (K := K) (target := target)
            (A := A) (pref := η.take P) (τ := τ) hpref hwt hτlen hcertPref
        simpa [hζeq] using hitem
      have hlengthItem :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) := by
        have hitem :
            (((A, η.take P ++ τ), w) : (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) :=
          NFYield.bounded_prefix_certificate_mem_bounded_length_items
            (g := g) (N := P) (K := K) (L := L)
            (A := A) (pref := η.take P) (τ := τ) hpref hwlen hτlen hcertPref
        simpa [hζeq] using hitem
      exact hreachable i hi hlow hup hhigh A η τ ζ u v q m w n'
        hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
        hζlen hζtake hζder hcert hreplacement hτmin htargetSurface
        hboundedSurface htargetItem hlengthItem)

/-- Full-prefix form of the certified prefix-preserving frontier bridge.

The certified finite-frontier data is still supplied to the local prefix-preservation premise,
but the remaining concrete reachability requirement is reduced to equality of the full visible
`Bpre` stack prefix. The stack-bounded prefix derivation is then built by
`exists_stackBoundedDerivesIn_late_window_context_take_eq`. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_context_take_eq
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
              P + (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card + 1 ≤
                Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 -
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ i →
                i ≤ trace.length - 1 -
                      (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card +
                    (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    η.take Bpre = ζ.take Bpre) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      have htake :
          η.take Bpre = ζ.take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      have hζBound : ζ.length ≤ Bpre := le_trans hζlen hPK
      exact
        exists_stackBoundedDerivesIn_late_window_context_take_eq
          (g := g) hNF (B := Bpre) (P := P)
          (C := (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card)
          (a := trace.length - 1 -
            (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card)
          (i := i) (j := i) htrace hhead hi hup hwindowBound hbeforeBound
          le_rfl hζBound hctx htake)

/-- Counted bounded-grammar reachability form of the certified prefix-preserving frontier
bridge.

The remaining prefix-reachability obligation is stated inside the bounded-stack grammar:
the encoded replacement context must be derivable from the compiled initial symbol within
the current prefix budget. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_boundedGrammarDerivesIn_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
                        ∃ p : ℕ,
                          p ≤ i ∧
                            grammar_derivesIn (boundedStackGrammar g Bpre) p
                              [symbol.nonterminal (boundedStackGrammar g Bpre).initial]
                              bw) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨bw, hbw, p, hpi, hp⟩ :=
        hreachable i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact ⟨p, hpi,
        stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential
          (g := g) (B := Bpre) hbw hp⟩)

/-- Finite-step-frontier form of the certified prefix-preserving late-window bridge.

This is the same generated-word conclusion as the bounded-grammar form, but the remaining
reachability premise is membership in the finite full-context bounded-sentential frontier
reachable within the current prefix budget. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_stepReachableSentential_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A ζ] ++ v) = some bw ∧
                        bw ∈
                          ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                            (∃ ys : List g.ISym,
                              ys ∈ boundedSententialForms g L Bpre ∧
                                boundedSentential? (g := g) Bpre ys = some bw) ∧
                              ∃ p : ℕ, p ≤ i ∧
                                grammar_derivesIn (boundedStackGrammar g Bpre) p
                                  [symbol.nonterminal
                                    (boundedStackGrammar g Bpre).initial] bw} :
                            Set (List (symbol T (BoundedStackNT g Bpre)))) ) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_boundedGrammarDerivesIn_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨bw, hbw, hfrontier⟩ :=
        hreachable i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact ⟨bw, hbw, hfrontier.2⟩)

/-- Full-surface-repeat form of the certified prefix-preserving late-window bridge.

The finite-step frontier premise is discharged by an earlier trace position whose full
`Bpre`-surface matches the certified prefix-preserving replacement context. The remaining
obligation is an actual ancestry/saturation statement over finite surface and certificate
frontiers. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_reachability
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
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_stepReachableSentential_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      have hζBound : ζ.length ≤ Bpre := le_trans hζlen hPK
      have hysStack :
          sententialMaxStackHeight (u ++ [ISym.indexed A ζ] ++ v) ≤ Bpre :=
        sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le
          (g := g) (u := u) (v := v) (A := A) (σ := ζ)
          hctxBound hζBound
      exact
        exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le
          (g := g) (P := P) (B := Bpre) (L := L) (N := i)
          (trace := trace) (ys := u ++ [ISym.indexed A ζ] ++ v)
          (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound
          hysStack hsurfaceEq hboundedSurface)

/-- Late-window form of the local replacement short-or-pop dichotomy. The late-window lower
bound converts the local suffix budget `q ≤ trace.length - 1 - i` into the uniform budget
`q ≤ C`, and the replacement equality normalizes the preserved prefix to `η.take P`. -/
theorem exists_bound_late_window_prefix_preserving_replacement_short_or_pop
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ) :
    ∃ Kpop : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          ∀ i : ℕ, i < trace.length →
            trace.length - 1 - C ≤ i →
            ∀ A : g.nt, ∀ η τ ζ : List g.flag,
              ∀ q m : ℕ, ∀ w : List T,
                w.Sublist target →
                q ≤ trace.length - 1 - i →
                m ≤ q →
                ζ = η.take P ++ τ →
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                (∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ.Sublist τ → ρ = τ) →
                τ.length ≤ Kpop ∨
                  ∃ n : ℕ,
                    m = n + 1 ∧
                      ((∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
                        ∃ r ∈ g.rules,
                          η.take P = [] ∧ τ = f :: ρ ∧
                          r.lhs = A ∧ r.consume = some f ∧
                          r.rhs = [IRhsSymbol.nonterminal B none] ∧
                          n < P + C ∧
                          g.DerivesIn n [ISym.indexed B ρ]
                            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
                      (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
                        ∃ r ∈ g.rules,
                          η.take P = f :: pref' ∧
                          pref'.length + n < P + C ∧
                          r.lhs = A ∧ r.consume = some f ∧
                          r.rhs = [IRhsSymbol.nonterminal B none] ∧
                          g.DerivesIn n [ISym.indexed B (pref' ++ τ)]
                            (w.map fun a => (ISym.terminal a : g.ISym)))) := by
  obtain ⟨Kpop, hKpop⟩ :=
    exists_bound_prefix_budget_forced_pop_dichotomy_target_length
      (g := g) hNF P C L
  refine ⟨Kpop, ?_⟩
  intro target htargetLen trace i hi hlow A η τ ζ q m w hwt hq hm hζeq hζder hτmin
  have hpref : (η.take P).length ≤ P := List.length_take_le P η
  have hqC : q ≤ C := by omega
  have hder :
      g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [hζeq] using hζder
  exact hKpop target htargetLen (η.take P) hpref q m A τ w hwt hm hqC hder hτmin

/-- Late-window direct boundedness for locally minimal prefix-preserving replacements.

The late-window inequality gives `q ≤ C`, hence the preserved prefix plus the local derivation
length is bounded by `P + C`. The locally budgeted minimal-suffix theorem then bounds the
replacement suffix directly, without exposing the intermediate pop descent. -/
theorem exists_bound_late_window_prefix_preserving_replacement_short_of_local_minimal
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ) :
    ∃ Kshort : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ trace : List (List g.ISym),
          ∀ i : ℕ, i < trace.length →
            trace.length - 1 - C ≤ i →
            ∀ A : g.nt, ∀ η τ ζ : List g.flag,
              ∀ q m : ℕ, ∀ w : List T,
                w.Sublist target →
                q ≤ trace.length - 1 - i →
                m ≤ q →
                ζ = η.take P ++ τ →
                g.DerivesIn m [ISym.indexed A ζ]
                  (w.map fun a => (ISym.terminal a : g.ISym)) →
                (∀ ρ : List g.flag, ∀ k : ℕ,
                  k ≤ q →
                  g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                    (w.map fun a => (ISym.terminal a : g.ISym)) →
                  ρ.Sublist τ → ρ = τ) →
                τ.length ≤ Kshort := by
  obtain ⟨Kmin, hKmin⟩ :=
    exists_bound_locally_budgeted_minimal_suffix_length_of_target_length_bounded_prefix_budget
      (g := g) hNF (P + C) L
  refine ⟨Kmin + (P + C), ?_⟩
  intro target htargetLen trace i hi hlow A η τ ζ q m w hwt hq hm hζeq hζder hτmin
  have hpref : (η.take P).length ≤ P + C := by
    exact le_trans (List.length_take_le P η) (Nat.le_add_right P C)
  have hqC : q ≤ C := by omega
  have hbudget : (η.take P).length + m ≤ P + C := by
    have hmC : m ≤ C := le_trans hm hqC
    have htake : (η.take P).length ≤ P := List.length_take_le P η
    omega
  have hder :
      g.DerivesIn m [ISym.indexed A (η.take P ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [hζeq] using hζder
  have hmin :
      ∀ ρ : List g.flag, ∀ k : ℕ,
        k ≤ m →
        g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        ρ.Sublist τ → ρ = τ := by
    intro ρ k hk hρder hρsub
    exact hτmin ρ k (le_trans hk hm) hρder hρsub
  exact hKmin target htargetLen (η.take P) hpref m A τ w hwt hder hmin hbudget

/-- Pop-descent package when the local pop consumes the first suffix flag below an empty
preserved prefix. The child derivation gives a child parse certificate, the parent's local
minimality descends to the child suffix, and the child item lies in both finite certificate
frontiers at the common bound `P + K`. -/
theorem empty_prefix_pop_child_certificate_frontiers_of_local_minimal
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P K L q n : ℕ} {target w : List T}
    {A B : g.nt} {f : g.flag} {pref τ ρ : List g.flag}
    {r : IRule T g.nt g.flag}
    (hwt : w.Sublist target) (hwlen : w.length ≤ L)
    (hnq : n + 1 ≤ q)
    (hpref : pref = []) (hτ : τ = f :: ρ) (hτlen : τ.length ≤ K)
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hchildDer :
      g.DerivesIn n [ISym.indexed B ρ]
        (w.map fun a => (ISym.terminal a : g.ISym)))
    (hmin : ∀ μ : List g.flag, ∀ k : ℕ,
      k ≤ q →
      g.DerivesIn k [ISym.indexed A (pref ++ μ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) →
      μ.Sublist τ → μ = τ) :
    NFYield g B ρ w ∧
      (∀ μ : List g.flag, ∀ k : ℕ,
        k ≤ n →
        g.DerivesIn k [ISym.indexed B μ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        μ.Sublist ρ → μ = ρ) ∧
      (((B, ρ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((B, ρ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
  have hchildCert : NFYield g B ρ w :=
    NFYield.of_derivesIn_isNormalForm (g := g) hNF hchildDer
  have hρlen : ρ.length ≤ K := by
    subst τ
    simp at hτlen ⊢
    omega
  have hchildMin :
      ∀ μ : List g.flag, ∀ k : ℕ,
        k ≤ n →
        g.DerivesIn k [ISym.indexed B μ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        μ.Sublist ρ → μ = ρ := by
    intro μ k hk hμder hμsub
    have hparent :
        g.DerivesIn (k + 1) [ISym.indexed A (pref ++ (f :: μ))]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      have hder :
          g.DerivesIn (k + 1) [ISym.indexed A (f :: μ)]
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
        apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
          (g := g) hNF (n := k) (A := A) (σ := f :: μ) (w := w)).mpr
        right
        left
        exact ⟨f, μ, B, r, hr, rfl, hlhs, hc, hrhs, hμder⟩
      simpa [hpref] using hder
    have hsub : (f :: μ).Sublist τ := by
      simpa [hτ] using List.Sublist.cons_cons f hμsub
    have heq := hmin (f :: μ) (k + 1) (by omega) hparent hsub
    have heq' : f :: μ = f :: ρ := by
      simpa [hτ] using heq
    exact (List.cons.inj heq').2
  have hprefBound : ([] : List g.flag).length ≤ P := by simp
  have htargetItem :
      (((B, ρ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
    have hitem :=
      NFYield.bounded_prefix_certificate_mem_bounded_target_items
        (g := g) (N := P) (K := K) (target := target)
        (A := B) (pref := ([] : List g.flag)) (τ := ρ)
        hprefBound hwt hρlen hchildCert
    simpa using hitem
  have hlengthItem :
      (((B, ρ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
    have hitem :=
      NFYield.bounded_prefix_certificate_mem_bounded_length_items
        (g := g) (N := P) (K := K) (L := L)
        (A := B) (pref := ([] : List g.flag)) (τ := ρ)
        hprefBound hwlen hρlen hchildCert
    simpa using hitem
  exact ⟨hchildCert, hchildMin, htargetItem, hlengthItem⟩

/-- Pop-descent package when the local pop consumes one preserved prefix flag. The child stays
under the shortened preserved prefix and the same suffix; local minimality and both finite
certificate-frontier memberships descend to that child obligation. -/
theorem prefix_pop_child_certificate_frontiers_of_local_minimal
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P K L q n : ℕ} {target w : List T}
    {A B : g.nt} {f : g.flag} {pref pref' τ : List g.flag}
    {r : IRule T g.nt g.flag}
    (hwt : w.Sublist target) (hwlen : w.length ≤ L)
    (hnq : n + 1 ≤ q)
    (hprefBound : pref.length ≤ P) (hpref : pref = f :: pref')
    (hτlen : τ.length ≤ K)
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hchildDer :
      g.DerivesIn n [ISym.indexed B (pref' ++ τ)]
        (w.map fun a => (ISym.terminal a : g.ISym)))
    (hmin : ∀ μ : List g.flag, ∀ k : ℕ,
      k ≤ q →
      g.DerivesIn k [ISym.indexed A (pref ++ μ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) →
      μ.Sublist τ → μ = τ) :
    NFYield g B (pref' ++ τ) w ∧
      (∀ μ : List g.flag, ∀ k : ℕ,
        k ≤ n →
        g.DerivesIn k [ISym.indexed B (pref' ++ μ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        μ.Sublist τ → μ = τ) ∧
      (((B, pref' ++ τ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((B, pref' ++ τ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
  have hchildCert : NFYield g B (pref' ++ τ) w :=
    NFYield.of_derivesIn_isNormalForm (g := g) hNF hchildDer
  have hpref'Bound : pref'.length ≤ P := by
    have hlen : (f :: pref').length ≤ P := by
      simpa [hpref] using hprefBound
    simp at hlen ⊢
    omega
  have hchildMin :
      ∀ μ : List g.flag, ∀ k : ℕ,
        k ≤ n →
        g.DerivesIn k [ISym.indexed B (pref' ++ μ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        μ.Sublist τ → μ = τ := by
    intro μ k hk hμder hμsub
    have hparent :
        g.DerivesIn (k + 1) [ISym.indexed A (pref ++ μ)]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
      have hder :
          g.DerivesIn (k + 1) [ISym.indexed A (f :: (pref' ++ μ))]
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
        apply (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
          (g := g) hNF (n := k) (A := A) (σ := f :: (pref' ++ μ)) (w := w)).mpr
        right
        left
        exact ⟨f, pref' ++ μ, B, r, hr, rfl, hlhs, hc, hrhs, hμder⟩
      simpa [hpref] using hder
    exact hmin μ (k + 1) (by omega) hparent hμsub
  have htargetItem :
      (((B, pref' ++ τ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) :=
    NFYield.bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := P) (K := K) (target := target)
      (A := B) (pref := pref') (τ := τ)
      hpref'Bound hwt hτlen hchildCert
  have hlengthItem :
      (((B, pref' ++ τ), w) : (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) :=
    NFYield.bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := P) (K := K) (L := L)
      (A := B) (pref := pref') (τ := τ)
      hpref'Bound hwlen hτlen hchildCert
  exact ⟨hchildCert, hchildMin, htargetItem, hlengthItem⟩

/-- Uniform child-descent form of the local short-or-pop dichotomy.

If the replacement suffix is not already short, the forced pop produces a child certificate in
the same finite certificate frontiers. The child's local rank `pref.length + steps` is strictly
smaller than the parent's rank `(η.take P).length + m`, so this is the induction-facing form of
the pop branch. -/
theorem short_or_pop_child_certificate_frontiers_of_local_minimal
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {P K Kpop L C q m : ℕ} {target w : List T}
    {A : g.nt} {η τ : List g.flag}
    (hwt : w.Sublist target) (hwlen : w.length ≤ L)
    (hm : m ≤ q) (hτlen : τ.length ≤ K)
    (hmin : ∀ μ : List g.flag, ∀ k : ℕ,
      k ≤ q →
      g.DerivesIn k [ISym.indexed A (η.take P ++ μ)]
        (w.map fun a => (ISym.terminal a : g.ISym)) →
      μ.Sublist τ → μ = τ)
    (hshortOrPop :
      τ.length ≤ Kpop ∨
        ∃ n₀ : ℕ,
          m = n₀ + 1 ∧
            ((∃ f : g.flag, ∃ ρ : List g.flag, ∃ Bchild : g.nt,
              ∃ r ∈ g.rules,
                η.take P = [] ∧ τ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal Bchild none] ∧
                n₀ < P + C ∧
                g.DerivesIn n₀ [ISym.indexed Bchild ρ]
                  (w.map fun a => (ISym.terminal a : g.ISym))) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ Bchild : g.nt,
              ∃ r ∈ g.rules,
                η.take P = f :: pref' ∧
                pref'.length + n₀ < P + C ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal Bchild none] ∧
                g.DerivesIn n₀ [ISym.indexed Bchild (pref' ++ τ)]
                  (w.map fun a => (ISym.terminal a : g.ISym))))) :
    τ.length ≤ Kpop ∨
      ∃ prefChild τChild : List g.flag, ∃ Bchild : g.nt, ∃ n₀ : ℕ,
        prefChild.length ≤ P ∧
          τChild.length ≤ K ∧
          prefChild.length + n₀ < (η.take P).length + m ∧
          NFYield g Bchild (prefChild ++ τChild) w ∧
          (∀ μ : List g.flag, ∀ k : ℕ,
            k ≤ n₀ →
            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            μ.Sublist τChild → μ = τChild) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) := by
  rcases hshortOrPop with hshort | hpop
  · exact Or.inl hshort
  rcases hpop with ⟨n₀, hmEq, hpop⟩
  have hnq : n₀ + 1 ≤ q := by
    rw [← hmEq]
    exact hm
  rcases hpop with hpopEmpty | hpopPrefix
  · rcases hpopEmpty with
      ⟨f, ρ, Bchild, r, hr, hpref, hτ, hlhs, hc, hrhs, _hbudget, hchildDer⟩
    obtain ⟨hcert, hchildMin, htargetItem, hlengthItem⟩ :=
      empty_prefix_pop_child_certificate_frontiers_of_local_minimal
        (g := g) hNF (P := P) (K := K) (L := L) (q := q) (n := n₀)
        (target := target) (w := w) (A := A) (B := Bchild) (f := f)
        (pref := η.take P) (τ := τ) (ρ := ρ) (r := r)
        hwt hwlen hnq hpref hτ hτlen hr hlhs hc hrhs hchildDer hmin
    have hρlen : ρ.length ≤ K := by
      rw [hτ] at hτlen
      simp at hτlen ⊢
      omega
    have hrank : ([] : List g.flag).length + n₀ < (η.take P).length + m := by
      rw [hpref, hmEq]
      simp
    refine Or.inr ⟨[], ρ, Bchild, n₀, by simp, hρlen, hrank, ?_, ?_, ?_, ?_⟩
    · simpa using hcert
    · simpa using hchildMin
    · simpa using htargetItem
    · simpa using hlengthItem
  · rcases hpopPrefix with
      ⟨f, pref', Bchild, r, hr, hpref, _hbudget, hlhs, hc, hrhs, hchildDer⟩
    have hprefBound : (η.take P).length ≤ P := List.length_take_le P η
    obtain ⟨hcert, hchildMin, htargetItem, hlengthItem⟩ :=
      prefix_pop_child_certificate_frontiers_of_local_minimal
        (g := g) hNF (P := P) (K := K) (L := L) (q := q) (n := n₀)
        (target := target) (w := w) (A := A) (B := Bchild) (f := f)
        (pref := η.take P) (pref' := pref') (τ := τ) (r := r)
        hwt hwlen hnq hprefBound hpref hτlen hr hlhs hc hrhs hchildDer hmin
    have hpref'Bound : pref'.length ≤ P := by
      have hlen : (f :: pref').length ≤ P := by
        simpa [hpref] using hprefBound
      simp at hlen ⊢
      omega
    have hrank : pref'.length + n₀ < (η.take P).length + m := by
      rw [hpref, hmEq]
      simp
      omega
    exact Or.inr
      ⟨pref', τ, Bchild, n₀, hpref'Bound, hτlen, hrank, hcert, hchildMin,
        htargetItem, hlengthItem⟩

/-- Package a rank-decreasing child certificate into the finite surface/certificate/rank
frontiers.

The child-descent lemma supplies the smaller local rank
`prefChild.length + n₀ < (η.take P).length + m`. If the parent rank is bounded by `R`, then the
child belongs to both finite rank frontiers paired with the same visible replacement surface. -/
theorem short_or_child_certificate_rank_frontiers_of_parent_rank_bound
    {g : IndexedGrammar T} {P K Kpop L R m : ℕ} {target w : List T}
    {η τ : List g.flag} {surface : SurfaceForm g P}
    (htargetSurface : surface ∈ targetCompatibleBoundedSurfaceForms g target P)
    (hlengthSurface : surface ∈ boundedSurfaceForms g L P)
    (hparentRank : (η.take P).length + m ≤ R)
    (hdescent :
      τ.length ≤ Kpop ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T))) :
    τ.length ≤ Kpop ∨
      ∃ prefChild τChild : List g.flag,
      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
        prefChild.length ≤ P ∧
          τChild.length ≤ K ∧
          prefChild.length + n₀ < (η.take P).length + m ∧
          NFYield g Bchild (prefChild ++ τChild) w ∧
          (∀ μ : List g.flag, ∀ k : ℕ,
            k ≤ n₀ →
            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            μ.Sublist τChild → μ = τChild) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) ∧
          (((surface, ((Bchild, prefChild ++ τChild), w)),
              prefChild.length + n₀) :
              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                x.1.2 ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                x.2 ≤ R} :
              Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) ∧
          (((surface, ((Bchild, prefChild ++ τChild), w)),
              prefChild.length + n₀) :
              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
              x.1.1 ∈ boundedSurfaceForms g L P ∧
                x.1.2 ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                x.2 ≤ R} :
              Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) := by
  rcases hdescent with hshort | hchild
  · exact Or.inl hshort
  rcases hchild with
    ⟨prefChild, τChild, Bchild, n₀, hpref, hτ, hrank, hcert, hmin, htargetItem,
      hlengthItem⟩
  have hchildRank : prefChild.length + n₀ ≤ R :=
    Nat.le_of_lt (lt_of_lt_of_le hrank hparentRank)
  have htargetRank :
      (((surface, ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
          (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
        ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
          x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
            x.1.2 ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            x.2 ≤ R} :
          Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) :=
    NFYield.bounded_target_surface_certificate_rank_mem
      (g := g) (P := P) (B := P + K) (R := R) (target := target)
      htargetSurface htargetItem hchildRank
  have hlengthRank :
      (((surface, ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
          (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
        ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
          x.1.1 ∈ boundedSurfaceForms g L P ∧
            x.1.2 ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            x.2 ≤ R} :
          Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) :=
    NFYield.bounded_length_surface_certificate_rank_mem
      (g := g) (P := P) (B := P + K) (L := L) (R := R)
      hlengthSurface hlengthItem hchildRank
  exact Or.inr
    ⟨prefChild, τChild, Bchild, n₀, hpref, hτ, hrank, hcert, hmin, htargetItem,
      hlengthItem, htargetRank, hlengthRank⟩

/-- The rank-aware short-or-child alternative is monotone in the suffix bound, forced-pop
threshold, and rank bound.

This is the transport needed when a later saturation argument works over an enlarged finite
frontier: the local descent proof may have been produced at stack budget `P + K` and rank
budget `R`, while the consuming frontier uses larger budgets. -/
theorem short_or_ranked_child_certificate_mono_bound
    {g : IndexedGrammar T} {P K K' Kpop Kpop' L R R' m : ℕ} {target w : List T}
    {η τ : List g.flag} {surface : SurfaceForm g P}
    (hK : K ≤ K') (hKpop : Kpop ≤ Kpop') (hR : R ≤ R')
    (hdescent :
      τ.length ≤ Kpop ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((surface, ((Bchild, prefChild ++ τChild), w)),
                prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ R} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) ∧
            (((surface, ((Bchild, prefChild ++ τChild), w)),
                prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ boundedSurfaceForms g L P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ R} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ))) :
    τ.length ≤ Kpop' ∨
      ∃ prefChild τChild : List g.flag,
      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
        prefChild.length ≤ P ∧
          τChild.length ≤ K' ∧
          prefChild.length + n₀ < (η.take P).length + m ∧
          NFYield g Bchild (prefChild ++ τChild) w ∧
          (∀ μ : List g.flag, ∀ k : ℕ,
            k ≤ n₀ →
            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
              (w.map fun a => (ISym.terminal a : g.ISym)) →
            μ.Sublist τChild → μ = τChild) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) ∧
          (((Bchild, prefChild ++ τChild), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) ∧
          (((surface, ((Bchild, prefChild ++ τChild), w)),
              prefChild.length + n₀) :
              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                x.1.2 ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                x.2 ≤ R'} :
              Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) ∧
          (((surface, ((Bchild, prefChild ++ τChild), w)),
              prefChild.length + n₀) :
              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
              x.1.1 ∈ boundedSurfaceForms g L P ∧
                x.1.2 ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                x.2 ≤ R'} :
              Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) := by
  rcases hdescent with hshort | hchild
  · exact Or.inl (le_trans hshort hKpop)
  rcases hchild with
    ⟨prefChild, τChild, Bchild, n₀, hpref, hτ, hrank, hcert, hmin, htargetItem,
      hlengthItem, htargetRank, hlengthRank⟩
  have hstack : P + K ≤ P + K' := Nat.add_le_add_left hK P
  have htargetItem' :
      (((Bchild, prefChild ++ τChild), w) :
          (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) :=
    NFYield.bounded_target_certificate_items_mono_bound
      (g := g) (B := P + K) (C := P + K') (target := target)
      hstack htargetItem
  have hlengthItem' :
      (((Bchild, prefChild ++ τChild), w) :
          (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) :=
    NFYield.bounded_length_certificate_items_mono_bound
      (g := g) (B := P + K) (C := P + K') (L := L)
      hstack hlengthItem
  have htargetRank' :
      (((surface, ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
          (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
        ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
          x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
            x.1.2 ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            x.2 ≤ R'} :
          Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) :=
    NFYield.bounded_target_surface_certificate_rank_items_mono_bound
      (g := g) (P := P) (B := P + K) (C := P + K') (R := R) (S := R')
      (target := target) hstack hR htargetRank
  have hlengthRank' :
      (((surface, ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
          (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
        ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
          x.1.1 ∈ boundedSurfaceForms g L P ∧
            x.1.2 ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            x.2 ≤ R'} :
          Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) :=
    NFYield.bounded_length_surface_certificate_rank_items_mono_bound
      (g := g) (P := P) (B := P + K) (C := P + K') (L := L) (R := R) (S := R')
      hstack hR hlengthRank
  exact Or.inr
    ⟨prefChild, τChild, Bchild, n₀, hpref, le_trans hτ hK, hrank, hcert, hmin,
      htargetItem', hlengthItem', htargetRank', hlengthRank'⟩

/-- Local late-window bridge from child descent to a rank-frontier surface-repeat premise.

The late-window inequalities imply `q ≤ C`; together with `m ≤ q` and
`(η.take P).length ≤ P`, the parent local rank is bounded by `P + C`. The plain child-descent
alternative can therefore be upgraded to the finite rank-frontier alternative expected by a
rank-aware surface-repeat argument. -/
theorem surfaceRepeat_of_late_window_child_descent_rank_frontier
    {g : IndexedGrammar T}
    {P K Kpop L C Bpre i q m : ℕ} {target w : List T}
    {trace : List (List g.ISym)} {A : g.nt} {η τ ζ : List g.flag}
    {u v : List g.ISym}
    (hlow : trace.length - 1 - C ≤ i)
    (hi : i < trace.length)
    (hq : q ≤ trace.length - 1 - i) (hm : m ≤ q)
    (htargetSurface :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
        targetCompatibleBoundedSurfaceForms g target P)
    (hlengthSurface :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
        boundedSurfaceForms g L P)
    (hdescent :
      τ.length ≤ Kpop ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)))
    (hsurfaceRepeat :
      (τ.length ≤ Kpop ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ P + C} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) ∧
            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ boundedSurfaceForms g L P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ P + C} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ))) →
      ∃ r : ℕ, ∃ hr : r < trace.length,
        r ≤ i ∧
          (∀ k (hk : k < trace.length),
            k ≤ r →
              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
          P + K ≤ Bpre ∧
          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
            surfaceOfTruncatedForm Bpre (u ++ [ISym.indexed A ζ] ++ v)) :
      ∃ r : ℕ, ∃ hr : r < trace.length,
        r ≤ i ∧
          (∀ k (hk : k < trace.length),
            k ≤ r →
              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
          P + K ≤ Bpre ∧
          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
            surfaceOfTruncatedForm Bpre (u ++ [ISym.indexed A ζ] ++ v) := by
  have hiPred : i ≤ trace.length - 1 := by
    simpa [Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hi
  have hqi : q + i ≤ trace.length - 1 :=
    (Nat.le_sub_iff_add_le hiPred).mp hq
  have hlow' : trace.length - 1 ≤ i + C :=
    Nat.sub_le_iff_le_add.mp hlow
  have hqC : q ≤ C := by omega
  have hparentRank : (η.take P).length + m ≤ P + C := by
    have hmC : m ≤ C := le_trans hm hqC
    have htake : (η.take P).length ≤ P := List.length_take_le P η
    omega
  exact hsurfaceRepeat
    (short_or_child_certificate_rank_frontiers_of_parent_rank_bound
      (g := g) (P := P) (K := K) (Kpop := Kpop) (L := L) (R := P + C)
      (m := m) (target := target) (w := w) (η := η) (τ := τ)
      (surface := surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v))
      htargetSurface hlengthSurface hparentRank hdescent)

/-- Monotone-budget form of `surfaceRepeat_of_late_window_child_descent_rank_frontier`.

The local late-window arithmetic packages child descent at the natural budget `P + C`. This
wrapper transports that ranked alternative to larger suffix and rank budgets before invoking
the surface-repeat premise. -/
theorem surfaceRepeat_of_late_window_child_descent_rank_frontier_mono
    {g : IndexedGrammar T}
    {P K K' Kpop Kpop' L C C' Bpre i q m : ℕ} {target w : List T}
    {trace : List (List g.ISym)} {A : g.nt} {η τ ζ : List g.flag}
    {u v : List g.ISym}
    (hK : K ≤ K') (hKpop : Kpop ≤ Kpop') (hC : C ≤ C')
    (hlow : trace.length - 1 - C ≤ i)
    (hi : i < trace.length)
    (hq : q ≤ trace.length - 1 - i) (hm : m ≤ q)
    (htargetSurface :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
        targetCompatibleBoundedSurfaceForms g target P)
    (hlengthSurface :
      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
        boundedSurfaceForms g L P)
    (hdescent :
      τ.length ≤ Kpop ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)))
    (hsurfaceRepeat :
      (τ.length ≤ Kpop' ∨
        ∃ prefChild τChild : List g.flag,
        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
          prefChild.length ≤ P ∧
            τChild.length ≤ K' ∧
            prefChild.length + n₀ < (η.take P).length + m ∧
            NFYield g Bchild (prefChild ++ τChild) w ∧
            (∀ μ : List g.flag, ∀ k : ℕ,
              k ≤ n₀ →
              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                (w.map fun a => (ISym.terminal a : g.ISym)) →
              μ.Sublist τChild → μ = τChild) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((Bchild, prefChild ++ τChild), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K') ∧ item.2.Sublist target ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ P + C'} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ)) ∧
            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                ((Bchild, prefChild ++ τChild), w)), prefChild.length + n₀) :
                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
              ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                x.1.1 ∈ boundedSurfaceForms g L P ∧
                  x.1.2 ∈
                    ({item : (g.nt × List g.flag) × List T |
                      item.1.2.length ≤ (P + K') ∧ item.2.length ≤ L ∧
                        NFYield g item.1.1 item.1.2 item.2} :
                      Set ((g.nt × List g.flag) × List T)) ∧
                  x.2 ≤ P + C'} :
                Set ((SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ))) →
      ∃ r : ℕ, ∃ hr : r < trace.length,
        r ≤ i ∧
          (∀ k (hk : k < trace.length),
            k ≤ r →
              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
          P + K' ≤ Bpre ∧
          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
            surfaceOfTruncatedForm Bpre (u ++ [ISym.indexed A ζ] ++ v)) :
      ∃ r : ℕ, ∃ hr : r < trace.length,
        r ≤ i ∧
          (∀ k (hk : k < trace.length),
            k ≤ r →
              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
          P + K' ≤ Bpre ∧
          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
            surfaceOfTruncatedForm Bpre (u ++ [ISym.indexed A ζ] ++ v) := by
  have hiPred : i ≤ trace.length - 1 := by
    simpa [Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hi
  have hqC : q ≤ C := by
    have hqi : q + i ≤ trace.length - 1 :=
      (Nat.le_sub_iff_add_le hiPred).mp hq
    have hlow' : trace.length - 1 ≤ i + C :=
      Nat.sub_le_iff_le_add.mp hlow
    omega
  have hparentRank : (η.take P).length + m ≤ P + C := by
    have hmC : m ≤ C := le_trans hm hqC
    have htake : (η.take P).length ≤ P := List.length_take_le P η
    omega
  have hranked :=
    short_or_child_certificate_rank_frontiers_of_parent_rank_bound
      (g := g) (P := P) (K := K) (Kpop := Kpop) (L := L) (R := P + C)
      (m := m) (target := target) (w := w) (η := η) (τ := τ)
      (surface := surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v))
      htargetSurface hlengthSurface hparentRank hdescent
  exact hsurfaceRepeat
    (short_or_ranked_child_certificate_mono_bound
      (g := g) (P := P) (K := K) (K' := K') (Kpop := Kpop) (Kpop' := Kpop')
      (L := L) (R := P + C) (R' := P + C') (m := m) (target := target)
      (w := w) (η := η) (τ := τ)
      (surface := surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v))
      hK hKpop (Nat.add_le_add_left hC P) hranked)

/-- Enlarged-budget generated-word form of the certified prefix-preserving surface-repeat
bridge.

The late-window budget `C` may be any finite frontier size dominating the visible
length-uniform surface frontier. The surface-repeat premise receives the certified
prefix-preserving replacement together with its visible-surface and finite certificate-item
memberships; from a matching full `Bpre`-surface it is converted internally into the
stack-bounded prefix required by the arbitrary-budget dichotomy. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_prefix_preserving_budget_max_stack
      (g := g) hNF P L C hC
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  let Bfinal := max (P + C) (Bpre + C)
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
  by_cases hgt : P + C < B
  · have hdich : n < C ∨ B ≤ Bpre + C := by
      exact hK target htargetLen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre hbeforeBound hgt
        (by
          intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx
            hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake
            hζder hcert hreplacement hτmin
          have htargetSurface :
              surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                targetCompatibleBoundedSurfaceForms g target P :=
            surfaceOfTruncatedForm_prefix_preserving_context_mem_targetCompatibleBoundedSurfaceForms
              (g := g) (P := P) (target := target) (trace := trace)
              hNF htrace hlast hi
              (u := u) (v := v) (A := A) (η := η) (ζ := ζ) hctx hζtake
          have hboundedSurface :
              surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                boundedSurfaceForms g L P :=
            surfaceOfTruncatedForm_prefix_preserving_context_mem_boundedSurfaceForms_lengthBound
              (g := g) (P := P) (L := L) (target := target) (trace := trace)
              hNF htrace hlast htargetLen hi
              (u := u) (v := v) (A := A) (η := η) (ζ := ζ) hctx hζtake
          have hpref : (η.take P).length ≤ P := List.length_take_le P η
          have hcertPref : NFYield g A (η.take P ++ τ) w := by
            simpa [hζeq] using hcert
          have htargetItem :
              (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                ({item : (g.nt × List g.flag) × List T |
                  item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                    NFYield g item.1.1 item.1.2 item.2} :
                  Set ((g.nt × List g.flag) × List T)) := by
            have hitem :
                (((A, η.take P ++ τ), w) : (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) :=
              NFYield.bounded_prefix_certificate_mem_bounded_target_items
                (g := g) (N := P) (K := K) (target := target)
                (A := A) (pref := η.take P) (τ := τ) hpref hwt hτlen hcertPref
            simpa [hζeq] using hitem
          have hlengthItem :
              (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                ({item : (g.nt × List g.flag) × List T |
                  item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                    NFYield g item.1.1 item.1.2 item.2} :
                  Set ((g.nt × List g.flag) × List T)) := by
            have hitem :
                (((A, η.take P ++ τ), w) : (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) :=
              NFYield.bounded_prefix_certificate_mem_bounded_length_items
                (g := g) (N := P) (K := K) (L := L)
                (A := A) (pref := η.take P) (τ := τ) hpref hwlen hτlen hcertPref
            simpa [hζeq] using hitem
          obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
            hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
              hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
              hζlen hζtake hζder hcert hreplacement hτmin htargetSurface
              hboundedSurface htargetItem hlengthItem
          have hζBound : ζ.length ≤ Bpre := le_trans hζlen hPK
          have hysStack :
              sententialMaxStackHeight (u ++ [ISym.indexed A ζ] ++ v) ≤ Bpre :=
            sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le
              (g := g) (u := u) (v := v) (A := A) (σ := ζ)
              hctxBound hζBound
          obtain ⟨bw, hbw, hfrontier⟩ :=
            exists_stepReachable_boundedSentential_image_of_context_surface_eq_prefix_bound_le
              (g := g) (P := P) (B := Bpre) (L := L) (N := i)
              (trace := trace) (ys := u ++ [ISym.indexed A ζ] ++ v)
              (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound
              hysStack hsurfaceEq hboundedSurface
          exact
            exists_stackBoundedDerivesIn_le_of_stepReachable_boundedSentential_image
              (g := g) (K := Bpre) (B := Bpre) (L := L) (N := i)
              (ys := u ++ [ISym.indexed A ζ] ++ v) (bw := bw) hbw hfrontier)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g C) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      simpa [Bfinal] using
        (boundedStackGrammar_language_mono
          (g := g) (B := C) (C := Bfinal) (by omega) target htargetC)
    · simpa [Bfinal] using
        (boundedStackGrammar_language_mono
          (g := g) (B := B) (C := Bfinal) (by omega) target htargetB)
  · simpa [Bfinal] using
      (boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB)

/-- Enlarged-budget generated-word bridge with the direct locally minimal suffix bound threaded
into the remaining surface-repeat premise.

The returned `K` is the common finite-frontier stack bound, enlarged to dominate both the
prefix-preserving shrinker bound and the direct late-window suffix bound `Kshort`. The premise
therefore receives certificate-item memberships at the common bound together with the concrete
`τ.length ≤ Kshort` evidence supplied by local minimality. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_short_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
    ∃ K Kshort : ℕ,
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    τ.length ≤ Kshort →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨Kshrink, hshrink⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_budget
      (g := g) hNF P L C hC
  obtain ⟨Kshort, hshort⟩ :=
    exists_bound_late_window_prefix_preserving_replacement_short_of_local_minimal
      (g := g) hNF P L C
  let K := max Kshrink Kshort
  refine ⟨K, Kshort, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hshrink target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      have hKshrink_le : Kshrink ≤ K := by
        dsimp [K]
        exact Nat.le_max_left Kshrink Kshort
      have hfrontier_le : P + Kshrink ≤ P + K := Nat.add_le_add_left hKshrink_le P
      have hτlenK : τ.length ≤ K := le_trans hτlen hKshrink_le
      have hζlenK : ζ.length ≤ P + K := le_trans hζlen hfrontier_le
      have htargetItemK :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_target_certificate_items_mono_bound
          (g := g) (B := P + Kshrink) (C := P + K) (target := target)
          hfrontier_le htargetItem
      have hlengthItemK :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_length_certificate_items_mono_bound
          (g := g) (B := P + Kshrink) (C := P + K) (L := L)
          hfrontier_le hlengthItem
      have hshortBound :=
        hshort target htargetLen trace i hi hlow A η τ ζ q m w
          hwt hq hm hζeq hζder hτmin
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlenK hζeq hζsub
          hζlenK hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItemK hlengthItemK hshortBound
      exact ⟨r, hr, hri, hprefixBound, hctxBound,
        le_trans hfrontier_le hPK, hsurfaceEq⟩)

/-- Enlarged-budget generated-word bridge with the local short-or-pop replacement dichotomy
threaded into the remaining surface-repeat premise.

The returned `K` is the common finite-frontier stack bound, enlarged to dominate both the
prefix-preserving shrinker bound and the forced-pop threshold `Kpop`. The premise therefore
receives certificate-item memberships at the common bound together with the concrete
`τ.length ≤ Kpop ∨ pop` evidence supplied by the counted local descent theorem. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_short_or_pop_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
    ∃ K Kpop : ℕ,
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ n₀ : ℕ,
                        m = n₀ + 1 ∧
                          ((∃ f : g.flag, ∃ ρ : List g.flag, ∃ Bchild : g.nt,
                            ∃ r ∈ g.rules,
                              η.take P = [] ∧ τ = f :: ρ ∧
                              r.lhs = A ∧ r.consume = some f ∧
                              r.rhs = [IRhsSymbol.nonterminal Bchild none] ∧
                              n₀ < P + C ∧
                              g.DerivesIn n₀ [ISym.indexed Bchild ρ]
                                (w.map fun a => (ISym.terminal a : g.ISym))) ∨
                          (∃ f : g.flag, ∃ pref' : List g.flag, ∃ Bchild : g.nt,
                            ∃ r ∈ g.rules,
                              η.take P = f :: pref' ∧
                              pref'.length + n₀ < P + C ∧
                              r.lhs = A ∧ r.consume = some f ∧
                              r.rhs = [IRhsSymbol.nonterminal Bchild none] ∧
                              g.DerivesIn n₀ [ISym.indexed Bchild (pref' ++ τ)]
                                (w.map fun a => (ISym.terminal a : g.ISym))))) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨Kshrink, hshrink⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_budget
      (g := g) hNF P L C hC
  obtain ⟨Kpop, hpop⟩ :=
    exists_bound_late_window_prefix_preserving_replacement_short_or_pop
      (g := g) hNF P L C
  let K := max Kshrink Kpop
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hshrink target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
      have hKshrink_le : Kshrink ≤ K := by
        dsimp [K]
        exact Nat.le_max_left Kshrink Kpop
      have hfrontier_le : P + Kshrink ≤ P + K := Nat.add_le_add_left hKshrink_le P
      have hτlenK : τ.length ≤ K := le_trans hτlen hKshrink_le
      have hζlenK : ζ.length ≤ P + K := le_trans hζlen hfrontier_le
      have htargetItemK :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_target_certificate_items_mono_bound
          (g := g) (B := P + Kshrink) (C := P + K) (target := target)
          hfrontier_le htargetItem
      have hlengthItemK :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_length_certificate_items_mono_bound
          (g := g) (B := P + Kshrink) (C := P + K) (L := L)
          hfrontier_le hlengthItem
      have hshortOrPop :=
        hpop target htargetLen trace i hi hlow A η τ ζ q m w
          hwt hq hm hζeq hζder hτmin
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlenK hζeq hζsub
          hζlenK hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItemK hlengthItemK hshortOrPop
      exact ⟨r, hr, hri, hprefixBound, hctxBound,
        le_trans hfrontier_le hPK, hsurfaceEq⟩)

/-- Generated-word bridge with the pop branch already converted to a rank-decreasing child
certificate obligation.

This is the saturation-facing form of
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_short_or_pop_budget`:
the remaining surface-repeat premise receives either the short replacement suffix or a child
certificate in the same finite frontiers whose local rank is strictly smaller than the parent
rank. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
    ∃ K Kpop : ℕ,
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T))) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_short_or_pop_budget
      (g := g) hNF P L C hC
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hshortOrPop
      have hdescent :=
        short_or_pop_child_certificate_frontiers_of_local_minimal
          (g := g) hNF (P := P) (K := K) (Kpop := Kpop) (L := L) (C := C)
          (q := q) (m := m) (target := target) (w := w) (A := A)
          (η := η) (τ := τ) hwt hwlen hm hτlen hτmin hshortOrPop
      exact
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface
          hboundedSurface htargetItem hlengthItem hdescent)

/-- Generated-word bridge with child descent packaged into finite rank frontiers.

This is the rank-saturation-facing version of
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_budget`.
The remaining surface-repeat premise receives either a short replacement suffix or a child
certificate whose smaller local rank is already registered in both finite rank frontiers. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
    ∃ K Kpop : ℕ,
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + C} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + C} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_budget
      (g := g) hNF P L C hC
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      exact
        surfaceRepeat_of_late_window_child_descent_rank_frontier
          (g := g) (P := P) (K := K) (Kpop := Kpop) (L := L) (C := C)
          (Bpre := Bpre) (i := i) (q := q) (m := m) (target := target)
          (w := w) (trace := trace) (A := A) (η := η) (τ := τ) (ζ := ζ)
          (u := u) (v := v) hlow hi hq hm htargetSurface hboundedSurface hdescent
          (by
            intro hrankedDescent
            exact
              hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
                hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
                hζlen hζtake hζder hcert hreplacement hτmin htargetSurface
                hboundedSurface htargetItem hlengthItem hrankedDescent))

/-- Generated-word bridge whose rank-aware surface-repeat premise may use enlarged finite
frontier budgets.

The shrinker still produces its intrinsic suffix and pop budgets `K` and `Kpop`. A later
saturation argument may choose larger certificate/rank frontiers after seeing those numbers;
this wrapper transports every local certificate item and ranked child alternative to those
larger budgets before invoking the supplied surface-repeat premise. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_budget_mono
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L C : ℕ)
    (hC : (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C) :
    ∃ K Kpop : ℕ,
      ∀ Ksat Kpopsat Csat : ℕ,
        K ≤ Ksat →
        Kpop ≤ Kpopsat →
        C ≤ Csat →
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
                  k < trace.length - 1 - C →
                    sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
                (∀ i : ℕ, ∀ hi : i < trace.length,
                  trace.length - 1 - C ≤ i →
                  i ≤ trace.length - 1 - C + C →
                  P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                      τ.length ≤ Ksat →
                      ζ = η.take P ++ τ →
                      ζ.Sublist η →
                      ζ.length ≤ P + Ksat →
                      ζ.take P = η.take P →
                      g.DerivesIn m [ISym.indexed A ζ]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      NFYield g A ζ w →
                      g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                        (target.map fun a => (ISym.terminal a : g.ISym)) →
                      (∀ ρ : List g.flag, ∀ k : ℕ,
                        k ≤ q →
                        g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                          (w.map fun a => (ISym.terminal a : g.ISym)) →
                        ρ.Sublist τ → ρ = τ) →
                      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                        targetCompatibleBoundedSurfaceForms g target P →
                      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                        boundedSurfaceForms g L P →
                      (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                        ({item : (g.nt × List g.flag) × List T |
                          item.1.2.length ≤ (P + Ksat) ∧ item.2.Sublist target ∧
                            NFYield g item.1.1 item.1.2 item.2} :
                          Set ((g.nt × List g.flag) × List T)) →
                      (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                        ({item : (g.nt × List g.flag) × List T |
                          item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                            NFYield g item.1.1 item.1.2 item.2} :
                          Set ((g.nt × List g.flag) × List T)) →
                      (τ.length ≤ Kpopsat ∨
                        ∃ prefChild τChild : List g.flag,
                        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                          prefChild.length ≤ P ∧
                            τChild.length ≤ Ksat ∧
                            prefChild.length + n₀ < (η.take P).length + m ∧
                            NFYield g Bchild (prefChild ++ τChild) w ∧
                            (∀ μ : List g.flag, ∀ k : ℕ,
                              k ≤ n₀ →
                              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                                (w.map fun a => (ISym.terminal a : g.ISym)) →
                              μ.Sublist τChild → μ = τChild) ∧
                            (((Bchild, prefChild ++ τChild), w) :
                                (g.nt × List g.flag) × List T) ∈
                              ({item : (g.nt × List g.flag) × List T |
                                item.1.2.length ≤ (P + Ksat) ∧ item.2.Sublist target ∧
                                  NFYield g item.1.1 item.1.2 item.2} :
                                Set ((g.nt × List g.flag) × List T)) ∧
                            (((Bchild, prefChild ++ τChild), w) :
                                (g.nt × List g.flag) × List T) ∈
                              ({item : (g.nt × List g.flag) × List T |
                                item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                                  NFYield g item.1.1 item.1.2 item.2} :
                                Set ((g.nt × List g.flag) × List T)) ∧
                            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                                ((Bchild, prefChild ++ τChild), w)),
                                prefChild.length + n₀) :
                                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                              ({x : (SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ |
                                x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                  x.1.2 ∈
                                    ({item : (g.nt × List g.flag) × List T |
                                      item.1.2.length ≤ (P + Ksat) ∧
                                        item.2.Sublist target ∧
                                        NFYield g item.1.1 item.1.2 item.2} :
                                      Set ((g.nt × List g.flag) × List T)) ∧
                                  x.2 ≤ P + Csat} :
                                Set ((SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                                ((Bchild, prefChild ++ τChild), w)),
                                prefChild.length + n₀) :
                                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                              ({x : (SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ |
                                x.1.1 ∈ boundedSurfaceForms g L P ∧
                                  x.1.2 ∈
                                    ({item : (g.nt × List g.flag) × List T |
                                      item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                                        NFYield g item.1.1 item.1.2 item.2} :
                                      Set ((g.nt × List g.flag) × List T)) ∧
                                  x.2 ≤ P + Csat} :
                                Set ((SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ))) →
                      ∃ r : ℕ, ∃ hr : r < trace.length,
                        r ≤ i ∧
                          (∀ k (hk : k < trace.length),
                            k ≤ r →
                              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                          P + Ksat ≤ Bpre ∧
                          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                            surfaceOfTruncatedForm Bpre
                              (u ++ [ISym.indexed A ζ] ++ v)) →
                target ∈
                  grammar_language
                    (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_budget
      (g := g) hNF P L C hC
  refine ⟨K, Kpop, ?_⟩
  intro Ksat Kpopsat Csat hKsat hKpopsat hCsat target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      have hstack : P + K ≤ P + Ksat := Nat.add_le_add_left hKsat P
      have htargetItemSat :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + Ksat) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_target_certificate_items_mono_bound
          (g := g) (B := P + K) (C := P + Ksat) (target := target)
          hstack htargetItem
      have hlengthItemSat :
          (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.bounded_length_certificate_items_mono_bound
          (g := g) (B := P + K) (C := P + Ksat) (L := L)
          hstack hlengthItem
      have hdescentSat :=
        short_or_ranked_child_certificate_mono_bound
          (g := g) (P := P) (K := K) (K' := Ksat) (Kpop := Kpop)
          (Kpop' := Kpopsat) (L := L) (R := P + C) (R' := P + Csat)
          (m := m) (target := target) (w := w) (η := η) (τ := τ)
          (surface := surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v))
          hKsat hKpopsat (Nat.add_le_add_left hCsat P) hdescent
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPKsat, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub
          (le_trans hτlen hKsat) hζeq hζsub (le_trans hζlen hstack) hζtake
          hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItemSat hlengthItemSat hdescentSat
      exact ⟨r, hr, hri, hprefixBound, hctxBound, le_trans hstack hPKsat,
        hsurfaceEq⟩)

/-- Generated-word bridge using the finite surface/certificate/rank frontier itself as the
late-window budget.

If the length ball contains a generated target, a root certificate embeds the visible
length-uniform surface frontier into this finite rank frontier. If it contains no generated
target, the generated-word conclusion is vacuous for the right reason: there is no word to
accept. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_frontier_budget_mono
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card
    ∃ K Kpop : ℕ,
      ∀ Ksat Kpopsat Csat : ℕ,
        K ≤ Ksat →
        Kpop ≤ Kpopsat →
        C ≤ Csat →
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
                  k < trace.length - 1 - C →
                    sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
                (∀ i : ℕ, ∀ hi : i < trace.length,
                  trace.length - 1 - C ≤ i →
                  i ≤ trace.length - 1 - C + C →
                  P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                  ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                      τ.length ≤ Ksat →
                      ζ = η.take P ++ τ →
                      ζ.Sublist η →
                      ζ.length ≤ P + Ksat →
                      ζ.take P = η.take P →
                      g.DerivesIn m [ISym.indexed A ζ]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      NFYield g A ζ w →
                      g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                        (target.map fun a => (ISym.terminal a : g.ISym)) →
                      (∀ ρ : List g.flag, ∀ k : ℕ,
                        k ≤ q →
                        g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                          (w.map fun a => (ISym.terminal a : g.ISym)) →
                        ρ.Sublist τ → ρ = τ) →
                      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                        targetCompatibleBoundedSurfaceForms g target P →
                      surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                        boundedSurfaceForms g L P →
                      (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                        ({item : (g.nt × List g.flag) × List T |
                          item.1.2.length ≤ (P + Ksat) ∧ item.2.Sublist target ∧
                            NFYield g item.1.1 item.1.2 item.2} :
                          Set ((g.nt × List g.flag) × List T)) →
                      (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                        ({item : (g.nt × List g.flag) × List T |
                          item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                            NFYield g item.1.1 item.1.2 item.2} :
                          Set ((g.nt × List g.flag) × List T)) →
                      (τ.length ≤ Kpopsat ∨
                        ∃ prefChild τChild : List g.flag,
                        ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                          prefChild.length ≤ P ∧
                            τChild.length ≤ Ksat ∧
                            prefChild.length + n₀ < (η.take P).length + m ∧
                            NFYield g Bchild (prefChild ++ τChild) w ∧
                            (∀ μ : List g.flag, ∀ k : ℕ,
                              k ≤ n₀ →
                              g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                                (w.map fun a => (ISym.terminal a : g.ISym)) →
                              μ.Sublist τChild → μ = τChild) ∧
                            (((Bchild, prefChild ++ τChild), w) :
                                (g.nt × List g.flag) × List T) ∈
                              ({item : (g.nt × List g.flag) × List T |
                                item.1.2.length ≤ (P + Ksat) ∧ item.2.Sublist target ∧
                                  NFYield g item.1.1 item.1.2 item.2} :
                                Set ((g.nt × List g.flag) × List T)) ∧
                            (((Bchild, prefChild ++ τChild), w) :
                                (g.nt × List g.flag) × List T) ∈
                              ({item : (g.nt × List g.flag) × List T |
                                item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                                  NFYield g item.1.1 item.1.2 item.2} :
                                Set ((g.nt × List g.flag) × List T)) ∧
                            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                                ((Bchild, prefChild ++ τChild), w)),
                                prefChild.length + n₀) :
                                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                              ({x : (SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ |
                                x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                  x.1.2 ∈
                                    ({item : (g.nt × List g.flag) × List T |
                                      item.1.2.length ≤ (P + Ksat) ∧
                                        item.2.Sublist target ∧
                                        NFYield g item.1.1 item.1.2 item.2} :
                                      Set ((g.nt × List g.flag) × List T)) ∧
                                  x.2 ≤ P + Csat} :
                                Set ((SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                            (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                                ((Bchild, prefChild ++ τChild), w)),
                                prefChild.length + n₀) :
                                (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                              ({x : (SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ |
                                x.1.1 ∈ boundedSurfaceForms g L P ∧
                                  x.1.2 ∈
                                    ({item : (g.nt × List g.flag) × List T |
                                      item.1.2.length ≤ (P + Ksat) ∧ item.2.length ≤ L ∧
                                        NFYield g item.1.1 item.1.2 item.2} :
                                      Set ((g.nt × List g.flag) × List T)) ∧
                                  x.2 ≤ P + Csat} :
                                Set ((SurfaceForm g P ×
                                  ((g.nt × List g.flag) × List T)) × ℕ))) →
                      ∃ r : ℕ, ∃ hr : r < trace.length,
                        r ≤ i ∧
                          (∀ k (hk : k < trace.length),
                            k ≤ r →
                              sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                          sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                          P + Ksat ≤ Bpre ∧
                          surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                            surfaceOfTruncatedForm Bpre
                              (u ++ [ISym.indexed A ζ] ++ v)) →
                target ∈
                  grammar_language
                    (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  by_cases hgenExists : ∃ target : List T, target.length ≤ L ∧ g.Generates target
  · have hC :
        (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤
          (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P Bcert L R)).card :=
      NFYield.boundedSurfaceForms_card_le_bounded_length_surface_certificate_rank_items_card_of_exists_generates_isNormalForm
        (g := g) (P := P) (B := Bcert) (L := L) (R := R) hNF hgenExists
    exact
      exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_budget_mono
        (g := g) hNF P L
        ((Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P Bcert L R)).card)
        hC
  · refine ⟨0, 0, ?_⟩
    intro Ksat Kpopsat Csat _hKsat _hKpopsat _hCsat target htargetLen hgen
    exact False.elim (hgenExists ⟨target, htargetLen, hgen⟩)

/-- Generated-word bridge with a concrete one-step saturated rank frontier.

The base late-window budget is the cardinality of the length-uniform rank frontier with
certificate stack/rank bounds `0, 0`. After the shrinker returns its intrinsic `K` and `Kpop`,
the surface-repeat premise is allowed to use the enlarged finite frontier with certificate
stack bound `P + K` and rank bound `P + C`. Cardinal monotonicity supplies the required
`C ≤ Csat` comparison. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_frontier_budget_mono
      (g := g) hNF P 0 0 L
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P 0 L 0)).card
  let Csat :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P (P + K) L (P + C))).card
  have hCCsat : C ≤ Csat := by
    dsimp [C, Csat]
    exact
      NFYield.bounded_length_surface_certificate_rank_items_card_mono_bound
        (g := g) (P := P) (B := 0) (C := P + K) (L := L) (R := 0)
        (S := P +
          (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P 0 L 0)).card)
        (Nat.zero_le (P + K)) (Nat.zero_le _)
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  exact
    hK K Kpop Csat le_rfl le_rfl hCCsat target htargetLen hgen

/-- Generated-word bridge with a concrete one-step saturated combined branch frontier.

This is the same rank-saturation bridge as
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_saturated_budget`,
but the late-window budget is the cardinality of the combined branch frontier: single
certificate/rank states plus binary pair/rank states. The consuming surface-repeat premise still
receives the single child-descent state required by the existing pop descent argument; the larger
budget leaves room for a later binary-pair saturation argument to use the same late window. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_branch_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A ζ] ++ v)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  by_cases hgenExists : ∃ target : List T, target.length ≤ L ∧ g.Generates target
  · let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P 0 L 0)).card
    have hC :
        (Set.Finite.toFinset (boundedSurfaceForms_finite g L P)).card ≤ C := by
      dsimp [C]
      exact
        NFYield.boundedSurfaceForms_card_le_bounded_length_surface_branch_rank_items_card_of_exists_generates_isNormalForm
          (g := g) (P := P) (B := 0) (L := L) (R := 0) hNF hgenExists
    obtain ⟨K, Kpop, hK⟩ :=
      exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_budget_mono
        (g := g) hNF P L C hC
    let Csat :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P (P + K) L (P + C))).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P (P + K) L (P + C))).card
    have hCCsat : C ≤ Csat := by
      dsimp [C, Csat]
      exact
        NFYield.bounded_length_surface_branch_rank_items_card_mono_bound
          (g := g) (P := P) (B := 0) (C := P + K) (L := L) (R := 0)
          (S := P +
            ((Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P 0 L 0)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                (g := g) P 0 L 0)).card))
          (Nat.zero_le (P + K)) (Nat.zero_le _)
    refine ⟨K, Kpop, ?_⟩
    intro target htargetLen hgen
    exact hK K Kpop Csat le_rfl le_rfl hCCsat target htargetLen hgen
  · refine ⟨0, 0, ?_⟩
    intro target htargetLen hgen
    exact False.elim (hgenExists ⟨target, htargetLen, hgen⟩)

/-- Full-prefix form of the saturated combined branch-frontier generated-word bridge.

This removes the abstract surface-repeat premise from
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_branch_descent_rank_saturated_budget`
when the certified replacement preserves the whole visible `Bpre` stack prefix. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_context_take_eq_branch_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    η.take Bpre = ζ.take Bpre) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_branch_descent_rank_saturated_budget
      (g := g) hNF P L
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      have htake :
          η.take Bpre = ζ.take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem hdescent
      exact
        exists_surface_repeat_at_current_of_late_window_context_take_eq
          (g := g) hNF (B := Bpre) (P := P) (K := K)
          (C :=
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_certificate_rank_items
                (g := g) P 0 L 0)).card +
            (Set.Finite.toFinset
              (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
                (g := g) P 0 L 0)).card)
          (i := i) (trace := trace) (u := u) (v := v) (A := A)
          (η := η) (ζ := ζ) htrace hhead hi hup hwindowBound hbeforeBound hPK
          hctx htake)

/-- Canonical suffix-prefix form of the saturated combined branch-frontier bridge.

For the canonical replacement `ζ = η.take P ++ τ`, preserving the next visible suffix segment
below the top `P` flags is enough to discharge the full-prefix premise required by the
saturated combined branch bridge. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_suffix_take_eq_branch_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    τ.take (Bpre - P) = (η.drop P).take (Bpre - P)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_context_take_eq_branch_descent_rank_saturated_budget
      (g := g) hNF P L
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK hsuffixPrefix
  exact hgenerated Bpre hbeforeBound hwindowBound hPK
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      have hsuffix :
          τ.take (Bpre - P) = (η.drop P).take (Bpre - P) :=
        hsuffixPrefix i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem hdescent
      have hPη : P ≤ η.length := by omega
      have hPB : P ≤ Bpre := by omega
      have htakeCanon :
          η.take Bpre = (η.take P ++ τ).take Bpre :=
        (stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm
      simpa [hζeq] using htakeCanon)

/-- Full-prefix form of the saturated rank-frontier generated-word bridge.

This removes the abstract surface-repeat premise from
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_saturated_budget`
when the certified replacement preserves the whole visible `Bpre` stack prefix. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_context_take_eq_child_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    η.take Bpre = ζ.take Bpre) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_surfaceRepeat_child_descent_rank_saturated_budget
      (g := g) hNF P L
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      have htake :
          η.take Bpre = ζ.take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem hdescent
      exact
        exists_surface_repeat_at_current_of_late_window_context_take_eq
          (g := g) hNF (B := Bpre) (P := P) (K := K)
          (C := (Set.Finite.toFinset
            (NFYield.finite_bounded_length_surface_certificate_rank_items
              (g := g) P 0 L 0)).card)
          (i := i) (trace := trace) (u := u) (v := v) (A := A)
          (η := η) (ζ := ζ) htrace hhead hi hup hwindowBound hbeforeBound hPK
          hctx htake)

/-- Canonical suffix-prefix form of the saturated rank-frontier generated-word bridge.

For the canonical replacement `ζ = η.take P ++ τ`, preserving the next visible suffix segment
below the top `P` flags is enough to discharge the full-prefix premise required by the
saturated rank bridge. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_suffix_take_eq_child_descent_rank_saturated_budget
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P 0 L 0)).card
    ∃ K Kpop : ℕ,
      let Csat :=
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_certificate_rank_items
            (g := g) P (P + K) L (P + C))).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
                P < sententialMaxStackHeight (trace.get ⟨i, hi⟩) →
                ∀ A : g.nt, ∀ η τ ζ : List g.flag,
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
                    ζ = η.take P ++ τ →
                    ζ.Sublist η →
                    ζ.length ≤ P + K →
                    ζ.take P = η.take P →
                    g.DerivesIn m [ISym.indexed A ζ]
                      (w.map fun a => (ISym.terminal a : g.ISym)) →
                    NFYield g A ζ w →
                    g.DerivesIn n' (u ++ [ISym.indexed A ζ] ++ v)
                      (target.map fun a => (ISym.terminal a : g.ISym)) →
                    (∀ ρ : List g.flag, ∀ k : ℕ,
                      k ≤ q →
                      g.DerivesIn k [ISym.indexed A (η.take P ++ ρ)]
                        (w.map fun a => (ISym.terminal a : g.ISym)) →
                      ρ.Sublist τ → ρ = τ) →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, ζ), w) : (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (τ.length ≤ Kpop ∨
                      ∃ prefChild τChild : List g.flag,
                      ∃ Bchild : g.nt, ∃ n₀ : ℕ,
                        prefChild.length ≤ P ∧
                          τChild.length ≤ K ∧
                          prefChild.length + n₀ < (η.take P).length + m ∧
                          NFYield g Bchild (prefChild ++ τChild) w ∧
                          (∀ μ : List g.flag, ∀ k : ℕ,
                            k ≤ n₀ →
                            g.DerivesIn k [ISym.indexed Bchild (prefChild ++ μ)]
                              (w.map fun a => (ISym.terminal a : g.ISym)) →
                            μ.Sublist τChild → μ = τChild) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((Bchild, prefChild ++ τChild), w) :
                              (g.nt × List g.flag) × List T) ∈
                            ({item : (g.nt × List g.flag) × List T |
                              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                NFYield g item.1.1 item.1.2 item.2} :
                              Set ((g.nt × List g.flag) × List T)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ targetCompatibleBoundedSurfaceForms g target P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧
                                      item.2.Sublist target ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ)) ∧
                          (((surfaceOfTruncatedForm P (u ++ [ISym.indexed A ζ] ++ v),
                              ((Bchild, prefChild ++ τChild), w)),
                              prefChild.length + n₀) :
                              (SurfaceForm g P × ((g.nt × List g.flag) × List T)) × ℕ) ∈
                            ({x : (SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ |
                              x.1.1 ∈ boundedSurfaceForms g L P ∧
                                x.1.2 ∈
                                  ({item : (g.nt × List g.flag) × List T |
                                    item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                                      NFYield g item.1.1 item.1.2 item.2} :
                                    Set ((g.nt × List g.flag) × List T)) ∧
                                x.2 ≤ P + Csat} :
                              Set ((SurfaceForm g P ×
                                ((g.nt × List g.flag) × List T)) × ℕ))) →
                    τ.take (Bpre - P) = (η.drop P).take (Bpre - P)) →
              target ∈
                grammar_language
                  (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  obtain ⟨K, Kpop, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_prefix_preserving_frontier_context_take_eq_child_descent_rank_saturated_budget
      (g := g) hNF P L
  refine ⟨K, Kpop, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK hsuffixPrefix
  exact hgenerated Bpre hbeforeBound hwindowBound hPK
    (by
      intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder hcert
        hreplacement hτmin htargetSurface hboundedSurface htargetItem hlengthItem
        hdescent
      have hsuffix :
          τ.take (Bpre - P) = (η.drop P).take (Bpre - P) :=
        hsuffixPrefix i hi hlow hup hhigh A η τ ζ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub
          hζlen hζtake hζder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem hdescent
      have hPη : P ≤ η.length := by omega
      have hPB : P ≤ Bpre := by omega
      have htakeCanon :
          η.take Bpre = (η.take P ++ τ).take Bpre :=
        (stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm
      simpa [hζeq] using htakeCanon)

/-- Explicit-budget generated-word form of the certified canonical late-window bridge using
the combined branch/rank frontier.

The late-window size is any `C` that dominates the finite length-uniform branch/rank frontier.
This is the saturation-ready form of
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_reachability`. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L C : ℕ)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C) :
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_branch_rank_budget_max_stack
      (g := g) hNF P Bcert R L C hC
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  let Bfinal := max (P + C) (Bpre + C)
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
  by_cases hgt : P + C < B
  · have hdich :
        n < C ∨ B ≤ Bpre + C := by
      exact hK target htargetLen hgen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre hbeforeBound hgt
        (by
          intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt
            hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder
            hcert hreplacement hτmin
          have hpre :=
            hreachable i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx
              hwt hwlen hq hm hmSuffix hn' hτsub hτlen
              (by simpa [hζeq] using hζder)
              (by simpa [hζeq] using hcert)
              (by simpa [hζeq] using hreplacement)
              hτmin
          simpa [hζeq] using hpre)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g C) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      exact boundedStackGrammar_language_mono
        (g := g) (B := C) (C := Bfinal) (by omega) target htargetC
    · exact boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB
  · exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) (by omega) target htargetB

/-- Explicit-budget full-surface-repeat form of the combined branch/rank canonical late-window
bridge.

The finite-window budget is supplied as an external `C` dominating the length-uniform
branch/rank frontier, while the remaining premise is an actual earlier trace position with the
same full `Bpre` surface as the canonical replacement context. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_surfaceRepeat_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L C : ℕ)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C) :
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_reachability
      (g := g) hNF P Bcert R L C hC
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
      have hηHigh : P < η.length := by
        simpa [hηmax] using hhigh
      have htargetSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            targetCompatibleBoundedSurfaceForms g target P :=
        surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms
          (g := g) (P := P) (target := target) (trace := trace)
          hNF htrace hlast hi (u := u) (v := v) (A := A) (η := η) (τ := τ)
          hctx hηHigh
      have hboundedSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            boundedSurfaceForms g L P :=
        surfaceOfTruncatedForm_canonical_context_mem_boundedSurfaceForms_lengthBound
          (g := g) (P := P) (L := L) (target := target) (trace := trace)
          hNF htrace hlast htargetLen hi
          (u := u) (v := v) (A := A) (η := η) (τ := τ) hctx hηHigh
      have htargetItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_target_items
          (g := g) (P := P) (K := K) (target := target)
          (A := A) (η := η) (τ := τ) hwt hτlen hcert
      have hlengthItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_length_items
          (g := g) (P := P) (K := K) (L := L)
          (A := A) (η := η) (τ := τ) hwlen hτlen hcert
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      obtain ⟨bw, hbw, hfrontier⟩ :=
        exists_stepReachable_boundedSentential_image_of_canonical_context_surface_eq_prefix_bound_le
          (g := g) (P := P) (K := K) (B := Bpre) (L := L) (N := i)
          (trace := trace) (u := u) (v := v) (A := A) (η := η) (τ := τ)
          (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound hctxBound hPK
          hτlen hsurfaceEq hboundedSurface
      exact
        exists_stackBoundedDerivesIn_le_of_stepReachable_boundedSentential_image
          (g := g) (K := Bpre) (B := Bpre) (L := L) (N := i)
          (ys := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) (bw := bw) hbw
          hfrontier)

/-- Explicit-budget full-prefix form of the combined branch/rank canonical late-window bridge.

This removes the full-surface-repeat premise from
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_surfaceRepeat_reachability`
when the canonical replacement preserves the whole visible `Bpre` stack prefix. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_context_take_eq_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L C : ℕ)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C) :
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    η.take Bpre = (η.take P ++ τ).take Bpre) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_surfaceRepeat_reachability
      (g := g) hNF P Bcert R L C hC
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      have htake :
          η.take Bpre = (η.take P ++ τ).take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact
        exists_surface_repeat_at_current_of_late_window_context_take_eq
          (g := g) hNF (B := Bpre) (P := P) (K := K) (C := C)
          (i := i) (trace := trace) (u := u) (v := v) (A := A)
          (η := η) (ζ := η.take P ++ τ)
          htrace hhead hi hup hwindowBound hbeforeBound hPK hctx htake)

/-- Explicit-budget canonical suffix-prefix form of the combined branch/rank late-window
bridge.

For the canonical replacement `η.take P ++ τ`, preserving the next visible suffix segment below
the top `P` flags is enough to discharge the full-prefix premise in the budgeted bridge. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_suffix_take_eq_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L C : ℕ)
    (hC :
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
        (Set.Finite.toFinset
          (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
            (g := g) P Bcert L R)).card ≤ C) :
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    τ.take (Bpre - P) = (η.drop P).take (Bpre - P)) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_budget_context_take_eq_reachability
      (g := g) hNF P Bcert R L C hC
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK hsuffixPrefix
  exact hgenerated Bpre hbeforeBound hwindowBound hPK
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      have hsuffix :
          τ.take (Bpre - P) = (η.drop P).take (Bpre - P) :=
        hsuffixPrefix i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      have hPη : P ≤ η.length := by omega
      have hPB : P ≤ Bpre := by omega
      exact
        (stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm)

/-- Generated-word form of the certified canonical late-window bridge using the combined
branch/rank frontier as the window budget.

This is the branch-aware analogue of
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_reachability`:
the fixed grammar bound is sized by the length-uniform frontier containing both single
certificate/rank states and binary pair/rank states. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P Bcert L R)).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P Bcert L R)).card +
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
        (g := g) P Bcert L R)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_steps_lt_or_minimal_stackBound_le_of_late_window_certificate_reachable_branch_rank_frontier_max_stack
      (g := g) hNF P Bcert R L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound⟩ :=
    exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
      (g := g) hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  let Bfinal := max (P + C) (Bpre + C)
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
  by_cases hgt : P + C < B
  · have hdich :
        n < C ∨ B ≤ Bpre + C := by
      exact hK target htargetLen hgen n B trace htrace hlen hhead hlast hminLength
        hminBound Bpre hbeforeBound
        (by simpa [C] using hgt)
        (by
          intro i hi hlow hup hhigh A η τ ζ u v q m w n' hmem hηmax hctx hwt
            hwlen hq hm hmSuffix hn' hτsub hτlen hζeq hζsub hζlen hζtake hζder
            hcert hreplacement hτmin
          have hpre :=
            hreachable i hi
              (by simpa [C] using hlow)
              (by simpa [C] using hup)
              hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen hq hm
              hmSuffix hn' hτsub hτlen
              (by simpa [hζeq] using hζder)
              (by simpa [hζeq] using hcert)
              (by simpa [hζeq] using hreplacement)
              hτmin
          simpa [hζeq] using hpre)
    rcases hdich with hnC | hBpre
    · have htargetC :
          target ∈ grammar_language (boundedStackGrammar g C) :=
        boundedStackGrammar_generates_of_derivesIn_isNormalForm_steps_le
          (g := g) hNF hder (Nat.le_of_lt hnC)
      exact boundedStackGrammar_language_mono
        (g := g) (B := C) (C := Bfinal) (by omega) target htargetC
    · exact boundedStackGrammar_language_mono
        (g := g) (B := B) (C := Bfinal) (by omega) target htargetB
  · exact boundedStackGrammar_language_mono
      (g := g) (B := B) (C := Bfinal) (by omega) target htargetB

/-- Full-surface-repeat form of the combined branch/rank canonical late-window bridge.

This threads the branch-aware finite-window budget through the same concrete prefix-repeat
reachability bridge used by the older surface-frontier wrapper. The remaining premise only has to
provide an earlier `Bpre`-bounded trace node with the same full `Bpre` surface as the canonical
replacement context; the bounded-stack prefix witness is then constructed internally. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_surfaceRepeat_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P Bcert L R)).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
                            (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v)) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P Bcert L R)).card +
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
        (g := g) P Bcert L R)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_reachability
      (g := g) hNF P Bcert R L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
      have hηHigh : P < η.length := by
        simpa [hηmax] using hhigh
      have htargetSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            targetCompatibleBoundedSurfaceForms g target P :=
        surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms
          (g := g) (P := P) (target := target) (trace := trace)
          hNF htrace hlast hi (u := u) (v := v) (A := A) (η := η) (τ := τ)
          hctx hηHigh
      have hboundedSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            boundedSurfaceForms g L P :=
        surfaceOfTruncatedForm_canonical_context_mem_boundedSurfaceForms_lengthBound
          (g := g) (P := P) (L := L) (target := target) (trace := trace)
          hNF htrace hlast htargetLen hi
          (u := u) (v := v) (A := A) (η := η) (τ := τ) hctx hηHigh
      have htargetItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_target_items
          (g := g) (P := P) (K := K) (target := target)
          (A := A) (η := η) (τ := τ) hwt hτlen hcert
      have hlengthItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_length_items
          (g := g) (P := P) (K := K) (L := L)
          (A := A) (η := η) (τ := τ) hwlen hτlen hcert
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      obtain ⟨bw, hbw, hfrontier⟩ :=
        exists_stepReachable_boundedSentential_image_of_canonical_context_surface_eq_prefix_bound_le
          (g := g) (P := P) (K := K) (B := Bpre) (L := L) (N := i)
          (trace := trace) (u := u) (v := v) (A := A) (η := η) (τ := τ)
          (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound hctxBound hPK
          hτlen hsurfaceEq hboundedSurface
      exact
        exists_stackBoundedDerivesIn_le_of_stepReachable_boundedSentential_image
          (g := g) (K := Bpre) (B := Bpre) (L := L) (N := i)
          (ys := u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) (bw := bw) hbw
          hfrontier)

/-- Full-prefix form of the combined branch/rank canonical late-window bridge.

This removes the abstract full-surface-repeat premise from
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_surfaceRepeat_reachability`
when the canonical replacement preserves the whole visible `Bpre` stack prefix. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_context_take_eq_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P Bcert L R)).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    η.take Bpre = (η.take P ++ τ).take Bpre) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P Bcert L R)).card +
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
        (g := g) P Bcert L R)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_surfaceRepeat_reachability
      (g := g) hNF P Bcert R L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK htakePrefix
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      have htake :
          η.take Bpre = (η.take P ++ τ).take Bpre :=
        htakePrefix i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact
        exists_surface_repeat_at_current_of_late_window_context_take_eq
          (g := g) hNF (B := Bpre) (P := P) (K := K) (C := C)
          (i := i) (trace := trace) (u := u) (v := v) (A := A)
          (η := η) (ζ := η.take P ++ τ)
          htrace hhead hi hup hwindowBound hbeforeBound hPK hctx htake)

/-- Canonical suffix-prefix form of the combined branch/rank late-window bridge.

For the canonical replacement `η.take P ++ τ`, preserving the next visible suffix segment below
the top `P` flags is enough to discharge the full-prefix premise. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_suffix_take_eq_reachability
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (P Bcert R L : ℕ) :
    let C :=
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_certificate_rank_items
          (g := g) P Bcert L R)).card +
      (Set.Finite.toFinset
        (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
          (g := g) P Bcert L R)).card
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
                k < trace.length - 1 - C →
                  sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ P) →
              P + C + 1 ≤ Bpre →
              P + K ≤ Bpre →
              (∀ i : ℕ, ∀ hi : i < trace.length,
                trace.length - 1 - C ≤ i →
                i ≤ trace.length - 1 - C + C →
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    τ.take (Bpre - P) = (η.drop P).take (Bpre - P)) →
              target ∈
                grammar_language (boundedStackGrammar g (max (P + C) (Bpre + C))) := by
  classical
  dsimp only
  let C :=
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_certificate_rank_items
        (g := g) P Bcert L R)).card +
    (Set.Finite.toFinset
      (NFYield.finite_bounded_length_surface_pair_certificate_rank_items
        (g := g) P Bcert L R)).card
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_branch_rank_frontier_context_take_eq_reachability
      (g := g) hNF P Bcert R L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hwindowBound hPK hsuffixPrefix
  exact hgenerated Bpre hbeforeBound hwindowBound hPK
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      have hsuffix :
          τ.take (Bpre - P) = (η.drop P).take (Bpre - P) :=
        hsuffixPrefix i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      have hPη : P ≤ η.length := by omega
      have hPB : P ≤ Bpre := by omega
      exact
        (stack_take_append_take_eq_of_suffix_take_eq hPη hPB hsuffix).symm)

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

/-- Frontier-facing generated-word form of the certified canonical late-window bridge.

This is the same fixed bounded-stack conclusion as
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_reachability`,
but the remaining reachability premise receives the actual proof that the canonical
replacement context has a visible `P`-surface in the finite target-compatible frontier and in
the length-uniform bounded-surface frontier. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_reachability
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
      have hηHigh : P < η.length := by
        simpa [hηmax] using hhigh
      have htargetSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            targetCompatibleBoundedSurfaceForms g target P :=
        surfaceOfTruncatedForm_canonical_context_mem_targetCompatibleBoundedSurfaceForms
          (g := g) (P := P) (target := target) (trace := trace)
          hNF htrace hlast hi (u := u) (v := v) (A := A) (η := η) (τ := τ)
          hctx hηHigh
      have hboundedSurface :
          surfaceOfTruncatedForm P
              (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
            boundedSurfaceForms g L P :=
        surfaceOfTruncatedForm_canonical_context_mem_boundedSurfaceForms_lengthBound
          (g := g) (P := P) (L := L) (target := target) (trace := trace)
          hNF htrace hlast htargetLen hi
          (u := u) (v := v) (A := A) (η := η) (τ := τ) hctx hηHigh
      have htargetItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_target_items
          (g := g) (P := P) (K := K) (target := target)
          (A := A) (η := η) (τ := τ) hwt hτlen hcert
      have hlengthItem :
          (((A, η.take P ++ τ), w) :
              (g.nt × List g.flag) × List T) ∈
            ({item : (g.nt × List g.flag) × List T |
              item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                NFYield g item.1.1 item.1.2 item.2} :
              Set ((g.nt × List g.flag) × List T)) :=
        NFYield.canonical_prefix_certificate_mem_bounded_length_items
          (g := g) (P := P) (K := K) (L := L)
          (A := A) (η := η) (τ := τ) hwlen hτlen hcert
      exact hreachable i hi hlow hup hhigh A η τ u v q m w n'
        hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
        hτder hcert hreplacement hτmin htargetSurface hboundedSurface
        htargetItem hlengthItem)

/-- Counted bounded-grammar reachability form of
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_reachability`.

The remaining prefix-reachability obligation is now stated inside the finite bounded-stack
grammar: the canonical replacement context must have a bounded encoding reachable from the
compiled initial symbol in at most the current prefix length. The conclusion is the same
fixed bounded-stack grammar acceptance statement. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_boundedGrammarDerivesIn_reachability
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) = some bw ∧
                        ∃ p : ℕ,
                          p ≤ i ∧
                            grammar_derivesIn (boundedStackGrammar g Bpre) p
                              [symbol.nonterminal (boundedStackGrammar g Bpre).initial]
                              bw) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨bw, hbw, p, hpi, hp⟩ :=
        hreachable i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact ⟨p, hpi,
        stackBoundedDerivesIn_of_boundedStackGrammar_derivesIn_initial_boundedSentential
          (g := g) (B := Bpre) hbw hp⟩)

/-- Finite-step-frontier form of the certified canonical late-window bridge.

This is the same generated-word conclusion as
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_boundedGrammarDerivesIn_reachability`,
but its remaining reachability premise is membership in the finite full-context sentential
frontier reachable within the current prefix budget. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_stepReachableSentential_reachability
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ bw : List (symbol T (BoundedStackNT g Bpre)),
                      boundedSentential? (g := g) Bpre
                          (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) = some bw ∧
                        bw ∈
                          ({bw : List (symbol T (BoundedStackNT g Bpre)) |
                            (∃ ys : List g.ISym,
                              ys ∈ boundedSententialForms g L Bpre ∧
                                boundedSentential? (g := g) Bpre ys = some bw) ∧
                              ∃ p : ℕ, p ≤ i ∧
                                grammar_derivesIn (boundedStackGrammar g Bpre) p
                                  [symbol.nonterminal
                                    (boundedStackGrammar g Bpre).initial] bw} :
                            Set (List (symbol T (BoundedStackNT g Bpre)))) ) →
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_boundedGrammarDerivesIn_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hreachable
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨bw, hbw, hfrontier⟩ :=
        hreachable i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact ⟨bw, hbw, hfrontier.2⟩)

/-- Full-surface-repeat form of the certified canonical late-window bridge.

The finite-step frontier premise in
`exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_stepReachableSentential_reachability`
is discharged by a concrete earlier trace position whose full `Bpre`-surface matches the
canonical replacement context, provided the prefix up to that earlier position is already
`Bpre`-bounded and the replacement context fits in `Bpre`. This isolates the remaining
ancestry/saturation task in terms of an actual trace repeat rather than an abstract
bounded-grammar reachability hypothesis. -/
theorem
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_surfaceRepeat_reachability
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
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      targetCompatibleBoundedSurfaceForms g target P →
                    surfaceOfTruncatedForm P
                        (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ∈
                      boundedSurfaceForms g L P →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.Sublist target ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    (((A, η.take P ++ τ), w) :
                        (g.nt × List g.flag) × List T) ∈
                      ({item : (g.nt × List g.flag) × List T |
                        item.1.2.length ≤ (P + K) ∧ item.2.length ≤ L ∧
                          NFYield g item.1.1 item.1.2 item.2} :
                        Set ((g.nt × List g.flag) × List T)) →
                    ∃ r : ℕ, ∃ hr : r < trace.length,
                      r ≤ i ∧
                        (∀ k (hk : k < trace.length),
                          k ≤ r →
                            sententialMaxStackHeight (trace.get ⟨k, hk⟩) ≤ Bpre) ∧
                        sententialMaxStackHeight (u ++ v) ≤ Bpre ∧
                        P + K ≤ Bpre ∧
                        surfaceOfTruncatedForm Bpre (trace.get ⟨r, hr⟩) =
                          surfaceOfTruncatedForm Bpre
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
    exists_bound_boundedStackGrammar_generates_of_late_window_certificate_canonical_frontier_stepReachableSentential_reachability
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen hgen
  obtain ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
      hminBound, hgenerated⟩ :=
    hK target htargetLen hgen
  refine ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound, ?_⟩
  intro Bpre hbeforeBound hsurfaceRepeat
  exact hgenerated Bpre hbeforeBound
    (by
      intro i hi hlow hup hhigh A η τ u v q m w n' hmem hηmax hctx hwt hwlen
        hq hm hmSuffix hn' hτsub hτlen hτder hcert hreplacement hτmin
        htargetSurface hboundedSurface htargetItem hlengthItem
      obtain ⟨r, hr, hri, hprefixBound, hctxBound, hPK, hsurfaceEq⟩ :=
        hsurfaceRepeat i hi hlow hup hhigh A η τ u v q m w n'
          hmem hηmax hctx hwt hwlen hq hm hmSuffix hn' hτsub hτlen
          hτder hcert hreplacement hτmin htargetSurface hboundedSurface
          htargetItem hlengthItem
      exact
        exists_stepReachable_boundedSentential_image_of_canonical_context_surface_eq_prefix_bound_le
          (g := g) (P := P) (K := K) (B := Bpre) (L := L) (N := i)
          (trace := trace) (u := u) (v := v) (A := A) (η := η) (τ := τ)
          (i := r) (j := i) htrace hhead hr hri le_rfl hprefixBound hctxBound hPK
          hτlen hsurfaceEq hboundedSurface)

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

/-- On every finite ball of terminal words, the per-word bounded-stack witnesses for a
normal-form grammar can be uniformized to a single fixed bounded-stack grammar. -/
theorem exists_uniform_boundedStackGrammar_generates_of_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ w : List T,
      w.length ≤ L →
      w ∈ g.Language →
      w ∈ grammar_language (boundedStackGrammar g B) := by
  classical
  let S : Set (List T) := {w | w.length ≤ L ∧ w ∈ g.Language}
  have hS : S.Finite :=
    (List.finite_length_le T L).subset (by
      intro w hw
      exact hw.1)
  have hExists :
      ∀ w : List T, w ∈ S →
        ∃ B : ℕ, w ∈ grammar_language (boundedStackGrammar g B) := by
    intro w hw
    exact exists_boundedStackGrammar_generates_of_generates_isNormalForm
      (g := g) hNF hw.2
  let boundOf : List T → ℕ := fun w =>
    if hw : w ∈ S then Classical.choose (hExists w hw) else 0
  have hboundOf :
      ∀ w : List T, ∀ hw : w ∈ S,
        w ∈ grammar_language (boundedStackGrammar g (boundOf w)) := by
    intro w hw
    dsimp [boundOf]
    rw [dif_pos hw]
    exact Classical.choose_spec (hExists w hw)
  refine ⟨(Set.Finite.toFinset hS).sup boundOf, ?_⟩
  intro w hlen hw
  have hwS : w ∈ S := ⟨hlen, hw⟩
  have hmem : w ∈ Set.Finite.toFinset hS := by
    rw [Set.Finite.mem_toFinset]
    exact hwS
  have hle : boundOf w ≤ (Set.Finite.toFinset hS).sup boundOf :=
    Finset.le_sup (s := Set.Finite.toFinset hS) (f := boundOf) hmem
  exact boundedStackGrammar_language_mono (g := g) hle w (hboundOf w hwS)

/-- On every finite ball of terminal words, a normal-form grammar agrees with one fixed
bounded-stack grammar.

The bound is obtained by finite choice over the finitely many generated words in the ball.
This removes the shortest-derivation-budget hypothesis from fixed-ball capture; the global
LBA core still needs a uniform machine construction rather than a separately chosen slice for
each input length. -/
theorem exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔
        target ∈ grammar_language (boundedStackGrammar g B)) := by
  obtain ⟨B, hB⟩ :=
    exists_uniform_boundedStackGrammar_generates_of_length_le_isNormalForm
      (g := g) hNF L
  refine ⟨B, ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    exact hB target htargetLen hgen
  · intro hbounded
    exact boundedStackGrammar_language_subset_language
      (g := g) (B := B) target hbounded

/-- Flat-path analogue of
`exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm`.
On every finite terminal ball, one fixed bounded flat-path slice agrees with the original
normal-form language. -/
theorem exists_bound_boundedFlatPathLanguage_eq_on_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔ target ∈ boundedFlatPathLanguage g B) := by
  obtain ⟨B, hB⟩ :=
    exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm
      (g := g) hNF L
  refine ⟨L * (B + 2), ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    exact boundedFlatPathLanguage_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := B) (L := L) htargetLen ((hB target htargetLen).mp hgen)
  · intro hflat
    exact boundedFlatPathLanguage_subset_language
      (g := g) (B := L * (B + 2)) hflat

/-- Exact-length flat-path finite-ball form of
`exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm`.

On a fixed terminal ball, one stack bound `B` suffices; each target word is then captured by
the flat search space whose tape bound is computed from that word's own length. -/
theorem exists_bound_boundedFlatPathLanguage_length_eq_on_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔
        target ∈ boundedFlatPathLanguage g (target.length * (B + 2))) := by
  obtain ⟨B, hB⟩ :=
    exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm
      (g := g) hNF L
  refine ⟨B, ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    exact boundedFlatPathLanguage_of_boundedStackGrammar_language_length_isNormalForm
      (g := g) hNF (B := B) ((hB target htargetLen).mp hgen)
  · intro hflat
    exact boundedFlatPathLanguage_subset_language
      (g := g) (B := target.length * (B + 2)) hflat

/-- Exact-length packed-reachability finite-ball form.

On a fixed terminal ball, one stack-width parameter `B` suffices; each nonempty target is then
captured by packed bounded-flat reachability over exactly `target.length` tape cells. -/
theorem exists_bound_packedFlatDerives_width_eq_on_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      ∀ htargetNe : target ≠ [],
      (target ∈ g.Language ↔
        PackedFlatDerives g (B + 2) target.length
          (packedBoundedFlatForm g (B + 2) target.length
            ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
              initial_mem_boundedFlatForms_length_mul_of_pos
                (g := g) (B := B) (w := target)
                (List.length_pos_of_ne_nil htargetNe)⟩)
          (packedBoundedFlatForm g (B + 2) target.length
            ⟨target.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
              terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) target⟩)) := by
  obtain ⟨B, hB⟩ :=
    exists_bound_boundedFlatPathLanguage_length_eq_on_length_le_isNormalForm
      (g := g) hNF L
  refine ⟨B, ?_⟩
  intro target htargetLen htargetNe
  rw [hB target htargetLen]
  exact boundedFlatPathLanguage_length_iff_packedFlatDerives
    (g := g) (B := B) (w := target) htargetNe

/-- Exact-length packed-language finite-ball form.

On a fixed terminal ball, one stack-bound parameter `B` makes the normal-form language agree
with the corresponding packed flat-path language. Unlike the raw packed reachability statement,
the packed language excludes `ε` internally, matching normal-form grammars. -/
theorem exists_bound_packedFlatPathStackBoundLanguage_eq_on_length_le_isNormalForm
    {g : IndexedGrammar T} [Fintype T] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔ target ∈ packedFlatPathStackBoundLanguage g B) := by
  obtain ⟨B, hB⟩ :=
    exists_bound_boundedFlatPathLanguage_length_eq_on_length_le_isNormalForm
      (g := g) hNF L
  refine ⟨B, ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    have htargetNe : target ≠ [] := by
      intro htarget
      subst target
      exact (g.not_generates_nil_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF)) hgen
    exact
      (packedFlatPathStackBoundLanguage_iff_boundedFlatPathLanguage_length
        (g := g) (B := B) (w := target)).mpr
        ⟨htargetNe, (hB target htargetLen).mp hgen⟩
  · intro hpacked
    exact (hB target htargetLen).mpr
      ((packedFlatPathStackBoundLanguage_iff_boundedFlatPathLanguage_length
        (g := g) (B := B) (w := target)).mp hpacked).2

/-- If shortest accepting derivations for all generated targets of length at most `L` are
bounded by `N`, then one fixed bounded-stack grammar captures the original normal-form
language exactly on that whole terminal ball.

This is the finite-ball form needed by the remaining simulator: the only open input is the
uniform shortest-derivation bound `hbudget`; the stack bound is then produced by the existing
shrinking construction and is independent of the particular target word. -/
theorem exists_bound_boundedStackGrammar_language_eq_on_length_le_of_minimal_derivesIn_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ)
    (hbudget : ∀ target : List T,
      target.length ≤ L →
      g.Generates target →
      ∀ n : ℕ,
        g.DerivesIn n [ISym.indexed g.initial []]
          (target.map fun a => (ISym.terminal a : g.ISym)) →
        (∀ m : ℕ,
          g.DerivesIn m [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
        n ≤ N) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔
        target ∈ grammar_language (boundedStackGrammar g B)) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_boundedStackGrammar_generates_of_minimal_derivesIn_target_length_budget
      (g := g) hNF N L
  refine ⟨N + K + N, ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
    exact hK target htargetLen n hder hmin
      (hbudget target htargetLen hgen n hder hmin)
  · intro hbounded
    exact boundedStackGrammar_language_subset_language
      (g := g) (B := N + K + N) target hbounded

/-- Flat-path analogue of
`exists_bound_boundedStackGrammar_language_eq_on_length_le_of_minimal_derivesIn_bound`.
Under a uniform shortest-derivation bound on the terminal ball of radius `L`, one finite flat
search slice captures the normal-form language exactly on that ball. -/
theorem exists_bound_boundedFlatPathLanguage_eq_on_length_le_of_minimal_derivesIn_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ)
    (hbudget : ∀ target : List T,
      target.length ≤ L →
      g.Generates target →
      ∀ n : ℕ,
        g.DerivesIn n [ISym.indexed g.initial []]
          (target.map fun a => (ISym.terminal a : g.ISym)) →
        (∀ m : ℕ,
          g.DerivesIn m [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
        n ≤ N) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔ target ∈ boundedFlatPathLanguage g B) := by
  obtain ⟨B, hB⟩ :=
    exists_bound_boundedStackGrammar_language_eq_on_length_le_of_minimal_derivesIn_bound
      (g := g) hNF N L hbudget
  refine ⟨L * (B + 2), ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    exact boundedFlatPathLanguage_of_boundedStackGrammar_language_isNormalForm
      (g := g) hNF (B := B) (L := L) htargetLen ((hB target htargetLen).mp hgen)
  · intro hflat
    exact boundedFlatPathLanguage_subset_language
      (g := g) (B := L * (B + 2)) hflat

/-- Direct flat-path finite-search slice under a uniform shortest-derivation budget.

This is the flat-search analogue of
`exists_bound_boundedFlatPathLanguage_eq_on_length_le_of_minimal_derivesIn_bound`, but it uses
the sharper step-budget flat bound exposed by
`exists_bound_bounded_accepting_flatPath_of_generates_target_length_stepFlatBound`.
It packages the current finite-ball simulator target without routing through a fixed
bounded-stack grammar first. -/
theorem exists_bound_boundedFlatPathLanguage_eq_on_length_le_of_minimal_derivesIn_stepFlatBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) (N L : ℕ)
    (hbudget : ∀ target : List T,
      target.length ≤ L →
      g.Generates target →
      ∀ n : ℕ,
        g.DerivesIn n [ISym.indexed g.initial []]
          (target.map fun a => (ISym.terminal a : g.ISym)) →
        (∀ m : ℕ,
          g.DerivesIn m [ISym.indexed g.initial []]
            (target.map fun a => (ISym.terminal a : g.ISym)) → n ≤ m) →
        n ≤ N) :
    ∃ B : ℕ, ∀ target : List T,
      target.length ≤ L →
      (target ∈ g.Language ↔ target ∈ boundedFlatPathLanguage g B) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_bounded_accepting_flatPath_of_generates_target_length_stepFlatBound
      (g := g) hNF N L
  refine ⟨L + L + (N + L * (N + K + N)), ?_⟩
  intro target htargetLen
  constructor
  · intro hgen
    obtain ⟨n, trace, ftrace, _hder, _hmin, _htrace, _hftrace, _hlen, _hhead,
        _hlast, _hflen, _hstack, hfhead, hflast, hfbound, hfstep, _hfderives,
        _hcard⟩ :=
      hK target htargetLen hgen (hbudget target htargetLen hgen)
    exact ⟨ftrace, hfhead, hflast, hfbound, hfstep⟩
  · intro hflat
    exact boundedFlatPathLanguage_subset_language
      (g := g) (B := L + L + (N + L * (N + K + N))) hflat

end IndexedGrammar
