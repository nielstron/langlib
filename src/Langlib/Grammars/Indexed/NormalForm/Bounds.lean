module

public import Langlib.Grammars.Indexed.Definition
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic
@[expose]
public section

/-! # Basic bounds for indexed normal form

These lemmas record the local length behavior of indexed grammars in normal form. They are
intended as infrastructure for the finite normal-form simulation used in the indexed-to-CS
inclusion.
-/

variable {T : Type}

namespace IndexedGrammar

/-! ## Finite directed reachability -/

/-- Exactly `n` directed steps along a relation. This counted form is used to put
finite-cardinality bounds on witnesses for reflexive-transitive reachability. -/
inductive RelDerivesIn {α : Type} (r : α → α → Prop) : ℕ → α → α → Prop where
  | zero (a : α) : RelDerivesIn r 0 a a
  | succ {n : ℕ} {a b c : α} :
      r a b → RelDerivesIn r n b c → RelDerivesIn r (n + 1) a c

namespace RelDerivesIn

variable {α : Type} {r : α → α → Prop} {a b c x : α} {n m i j : ℕ}

theorem reflTransGen (h : RelDerivesIn r n a b) : Relation.ReflTransGen r a b := by
  induction h with
  | zero a => exact Relation.ReflTransGen.refl
  | succ hstep _ ih => exact Relation.ReflTransGen.head hstep ih

theorem exists_of_reflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ n : ℕ, RelDerivesIn r n a b := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨0, zero b⟩
  · intro a c hac _ ih
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, succ hac hn⟩

theorem trans (h₁ : RelDerivesIn r n a b) (h₂ : RelDerivesIn r m b c) :
    RelDerivesIn r (n + m) a c := by
  induction h₁ generalizing m c with
  | zero a =>
      simpa using h₂
  | succ hstep _ ih =>
      convert succ hstep (ih h₂) using 1
      omega

theorem split (h : RelDerivesIn r n a b) (hi : i ≤ n) :
    ∃ x : α, RelDerivesIn r i a x ∧ RelDerivesIn r (n - i) x b := by
  induction i generalizing a n with
  | zero =>
      exact ⟨a, zero a, by simpa using h⟩
  | succ i ih =>
      cases h with
      | zero a =>
          omega
      | @succ n₀ a₀ b₀ c₀ hstep hrest =>
          have hi' : i ≤ n₀ := by omega
          obtain ⟨x, hpre, hsuf⟩ := ih hrest hi'
          exact ⟨x, succ hstep hpre, by simpa [Nat.succ_sub_succ_eq_sub] using hsuf⟩

theorem minimal_intermediate_index_eq
    (hmin : ∀ m : ℕ, RelDerivesIn r m a b → n ≤ m)
    (hi : i ≤ n) (hj : j ≤ n)
    (hprei : RelDerivesIn r i a x) (hsufi : RelDerivesIn r (n - i) x b)
    (hprej : RelDerivesIn r j a x) (hsufj : RelDerivesIn r (n - j) x b) :
    i = j := by
  rcases lt_trichotomy i j with hij | h | hji
  · have hshort : RelDerivesIn r (i + (n - j)) a b := trans hprei hsufj
    have hshort_lt : i + (n - j) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)
  · exact h
  · have hshort : RelDerivesIn r (j + (n - i)) a b := trans hprej hsufi
    have hshort_lt : j + (n - i) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)

/-- Any finite directed reachability witness can be chosen with at most as many vertices as
the whole finite state space. -/
theorem exists_card_bound_of_reflTransGen [Fintype α]
    (h : Relation.ReflTransGen r a b) :
    ∃ n : ℕ, RelDerivesIn r n a b ∧ n + 1 ≤ Fintype.card α := by
  classical
  obtain ⟨n₀, hn₀⟩ := exists_of_reflTransGen h
  let P : ℕ → Prop := fun k => RelDerivesIn r k a b
  have hP : ∃ k : ℕ, P k := ⟨n₀, hn₀⟩
  let n := Nat.find hP
  have hn : RelDerivesIn r n a b := Nat.find_spec hP
  have hmin : ∀ m : ℕ, RelDerivesIn r m a b → n ≤ m := by
    intro m hm
    exact Nat.find_min' hP hm
  let mid : Fin (n + 1) → α := fun k =>
    Classical.choose (split hn (i := k.1) (by omega))
  have hmid :
      ∀ k : Fin (n + 1),
        RelDerivesIn r k.1 a (mid k) ∧ RelDerivesIn r (n - k.1) (mid k) b := by
    intro k
    exact Classical.choose_spec (split hn (i := k.1) (by omega))
  have hinj : Function.Injective mid := by
    intro p q hpq
    apply Fin.ext
    have hp := hmid p
    have hq := hmid q
    exact minimal_intermediate_index_eq (r := r) (a := a) (b := b) (n := n)
      (x := mid p) hmin (by omega) (by omega) hp.1 hp.2
      (by simpa [hpq] using hq.1) (by simpa [hpq] using hq.2)
  have hcard := Fintype.card_le_of_injective mid hinj
  exact ⟨n, hn, by simpa using hcard⟩

theorem exists_chain (h : RelDerivesIn r n a b) :
    ∃ path : List α,
      path.length = n + 1 ∧
      path.head? = some a ∧
      path.getLast? = some b ∧
      path.IsChain r := by
  induction h with
  | zero a =>
      exact ⟨[a], by simp, by simp, by simp, List.isChain_singleton a⟩
  | @succ n₀ a₀ b₀ c₀ hstep hrest ih =>
      obtain ⟨path, hlen, hhead, hlast, hchain⟩ := ih
      cases path with
      | nil =>
          simp at hlen
      | cons p ps =>
          have hp : p = b₀ := by
            simpa using hhead
          subst p
          refine ⟨a₀ :: b₀ :: ps, ?_, ?_, ?_, ?_⟩
          · simp [hlen, Nat.add_assoc]
          · simp
          · simpa using hlast
          · exact List.IsChain.cons_cons hstep hchain

end RelDerivesIn

/-! ## Sentential-form measures -/

def ISym.isIndexed {g : IndexedGrammar T} : g.ISym → Bool
  | ISym.terminal _ => false
  | ISym.indexed _ _ => true

def ISym.isTerminal {g : IndexedGrammar T} : g.ISym → Bool
  | ISym.terminal _ => true
  | ISym.indexed _ _ => false

def ISym.toTerminal? {g : IndexedGrammar T} : g.ISym → Option T
  | ISym.terminal a => some a
  | ISym.indexed _ _ => none

def ISym.stackHeight {g : IndexedGrammar T} : g.ISym → ℕ
  | ISym.terminal _ => 0
  | ISym.indexed _ σ => σ.length

def sententialTerminals {g : IndexedGrammar T} (w : List g.ISym) : List T :=
  w.filterMap ISym.toTerminal?

def sententialNonterminalCount {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  w.countP ISym.isIndexed

def sententialTerminalCount {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  w.countP ISym.isTerminal

def sententialStackHeight {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  (w.map ISym.stackHeight).sum

def sententialMaxStackHeight {g : IndexedGrammar T} : List g.ISym → ℕ
  | [] => 0
  | s :: w => max s.stackHeight (sententialMaxStackHeight w)

/-! ## Flat tape encoding -/

/-- Finite tape alphabet used to flatten indexed sentential forms: terminals stay terminals,
an indexed nonterminal is encoded as its nonterminal head, followed by its stack flags, followed
by a boundary marker. -/
public inductive FlatSymbol (T N F : Type) where
  | terminal : T → FlatSymbol T N F
  | nonterminal : N → FlatSymbol T N F
  | flag : F → FlatSymbol T N F
  | stackBottom : FlatSymbol T N F
deriving DecidableEq, Fintype

namespace FlatSymbol

def toTerminal? {T N F : Type} : FlatSymbol T N F → Option T
  | terminal a => some a
  | nonterminal _ => none
  | flag _ => none
  | stackBottom => none

@[simp] theorem toTerminal?_terminal {N F : Type} (a : T) :
    toTerminal? (N := N) (F := F) (FlatSymbol.terminal a) = some a := rfl

@[simp] theorem toTerminal?_nonterminal {N F : Type} (A : N) :
    toTerminal? (T := T) (F := F) (FlatSymbol.nonterminal A) = none := rfl

@[simp] theorem toTerminal?_flag {N F : Type} (f : F) :
    toTerminal? (T := T) (N := N) (FlatSymbol.flag f) = none := rfl

@[simp] theorem toTerminal?_stackBottom {N F : Type} :
    toTerminal? (T := T) (N := N) (F := F) FlatSymbol.stackBottom = none := rfl

end FlatSymbol

/-- Flatten one indexed symbol into a word over the finite tape alphabet. -/
def encodeISym {g : IndexedGrammar T} : g.ISym → List (FlatSymbol T g.nt g.flag)
  | ISym.terminal a => [FlatSymbol.terminal a]
  | ISym.indexed A σ => FlatSymbol.nonterminal A :: σ.map FlatSymbol.flag ++
      [FlatSymbol.stackBottom]

/-- Flatten a whole indexed sentential form. -/
def encodeSentential {g : IndexedGrammar T}
    (w : List g.ISym) : List (FlatSymbol T g.nt g.flag) :=
  w.flatMap encodeISym

@[simp] theorem encodeISym_terminal {g : IndexedGrammar T} (a : T) :
    encodeISym (g := g) (ISym.terminal a) = [FlatSymbol.terminal a] := rfl

@[simp] theorem encodeISym_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    encodeISym (g := g) (ISym.indexed A σ) =
      FlatSymbol.nonterminal A :: σ.map FlatSymbol.flag ++ [FlatSymbol.stackBottom] := rfl

@[simp] theorem encodeSentential_nil {g : IndexedGrammar T} :
    encodeSentential ([] : List g.ISym) = [] := rfl

@[simp] theorem encodeSentential_cons {g : IndexedGrammar T} (s : g.ISym)
    (w : List g.ISym) :
    encodeSentential (s :: w) = encodeISym s ++ encodeSentential w := rfl

@[simp] theorem encodeSentential_singleton {g : IndexedGrammar T} (s : g.ISym) :
    encodeSentential [s] = encodeISym s := by
  simp [encodeSentential]

@[simp] theorem encodeSentential_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    encodeSentential (u ++ v) = encodeSentential u ++ encodeSentential v := by
  simp [encodeSentential, List.flatMap_append]

@[simp] theorem encodeISym_length_terminal {g : IndexedGrammar T} (a : T) :
    (encodeISym (g := g) (ISym.terminal a)).length = 1 := rfl

@[simp] theorem encodeISym_length_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    (encodeISym (g := g) (ISym.indexed A σ)).length = σ.length + 2 := by
  simp [encodeISym]

theorem encodeISym_ne_nil {g : IndexedGrammar T} (s : g.ISym) :
    encodeISym s ≠ [] := by
  cases s <;> simp [encodeISym]

@[simp] theorem encodeSentential_initial {g : IndexedGrammar T} :
    encodeSentential ([ISym.indexed g.initial []] : List g.ISym) =
      [FlatSymbol.nonterminal g.initial, FlatSymbol.stackBottom] := by
  simp [encodeSentential, encodeISym]

@[simp] theorem encodeSentential_initial_length {g : IndexedGrammar T} :
    (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)).length = 2 := by
  simp

@[simp] theorem encodeSentential_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    encodeSentential (w.map fun a => (ISym.terminal a : g.ISym)) =
      w.map FlatSymbol.terminal := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

@[simp] theorem encodeSentential_length_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    (encodeSentential (w.map fun a => (ISym.terminal a : g.ISym))).length = w.length := by
  simp

@[simp] theorem flatSymbol_terminals_map_terminal {N F : Type} (w : List T) :
    (w.map (FlatSymbol.terminal (N := N) (F := F))).filterMap
        FlatSymbol.toTerminal? = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

@[simp] theorem encodeSentential_final_terminals {g : IndexedGrammar T}
    (w : List T) :
    (encodeSentential (w.map fun a => (ISym.terminal a : g.ISym))).filterMap
        FlatSymbol.toTerminal? = w := by
  simp [Function.comp_def]

@[simp] theorem encodeISym_terminals {g : IndexedGrammar T} (s : g.ISym) :
    (encodeISym s).filterMap FlatSymbol.toTerminal? =
      sententialTerminals ([s] : List g.ISym) := by
  cases s <;> simp [encodeISym, sententialTerminals, FlatSymbol.toTerminal?, ISym.toTerminal?]

@[simp] theorem encodeSentential_terminals {g : IndexedGrammar T}
    (w : List g.ISym) :
    (encodeSentential w).filterMap FlatSymbol.toTerminal? = sententialTerminals w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      rw [encodeSentential_cons, List.filterMap_append, encodeISym_terminals, ih]
      cases s <;> simp [sententialTerminals, ISym.toTerminal?]

def decodeFlatStack {N F : Type} :
    List (FlatSymbol T N F) → Option (List F × List (FlatSymbol T N F))
  | [] => none
  | FlatSymbol.stackBottom :: rest => some ([], rest)
  | FlatSymbol.flag f :: rest =>
      match decodeFlatStack rest with
      | some (σ, rest') => some (f :: σ, rest')
      | none => none
  | FlatSymbol.terminal _ :: _ => none
  | FlatSymbol.nonterminal _ :: _ => none

@[simp] theorem decodeFlatStack_flags_append {N F : Type}
    (σ : List F) (rest : List (FlatSymbol T N F)) :
    decodeFlatStack (σ.map FlatSymbol.flag ++ FlatSymbol.stackBottom :: rest) =
      some (σ, rest) := by
  induction σ with
  | nil => rfl
  | cons f σ ih =>
      simp [decodeFlatStack, ih]

theorem encodeFlatStack_of_decodeFlatStack_eq_some {N F : Type}
    {x : List (FlatSymbol T N F)} {σ : List F} {rest : List (FlatSymbol T N F)}
    (h : decodeFlatStack x = some (σ, rest)) :
    x = σ.map FlatSymbol.flag ++ FlatSymbol.stackBottom :: rest := by
  induction x generalizing σ rest with
  | nil =>
      simp [decodeFlatStack] at h
  | cons a xs ih =>
      cases a with
      | terminal a =>
          simp [decodeFlatStack] at h
      | nonterminal A =>
          simp [decodeFlatStack] at h
      | flag f =>
          cases htail : decodeFlatStack xs with
          | none =>
              simp [decodeFlatStack, htail] at h
          | some p =>
              rcases p with ⟨τ, rest'⟩
              simp [decodeFlatStack, htail] at h
              rcases h with ⟨hσ, hrest⟩
              subst σ
              subst rest
              rw [ih htail]
              rfl
      | stackBottom =>
          simp [decodeFlatStack] at h
          rcases h with ⟨rfl, rfl⟩
          rfl

def decodeFlatSententialAux {g : IndexedGrammar T} :
    ℕ → List (FlatSymbol T g.nt g.flag) → Option (List g.ISym)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | n + 1, FlatSymbol.terminal a :: rest =>
      match decodeFlatSententialAux n rest with
      | some w => some (ISym.terminal a :: w)
      | none => none
  | n + 1, FlatSymbol.nonterminal A :: rest =>
      match decodeFlatStack rest with
      | some (σ, rest') =>
          match decodeFlatSententialAux n rest' with
          | some w => some (ISym.indexed A σ :: w)
          | none => none
      | none => none
  | _ + 1, FlatSymbol.flag _ :: _ => none
  | _ + 1, FlatSymbol.stackBottom :: _ => none

def decodeFlatSentential {g : IndexedGrammar T}
    (w : List (FlatSymbol T g.nt g.flag)) : Option (List g.ISym) :=
  decodeFlatSententialAux w.length w

theorem encodeSentential_of_decodeFlatSententialAux_eq_some {g : IndexedGrammar T} :
    ∀ n : ℕ, ∀ x : List (FlatSymbol T g.nt g.flag), ∀ w : List g.ISym,
      decodeFlatSententialAux n x = some w → encodeSentential w = x := by
  intro n
  induction n with
  | zero =>
      intro x w h
      cases x with
      | nil =>
          simp [decodeFlatSententialAux] at h
          subst w
          rfl
      | cons a xs =>
          simp [decodeFlatSententialAux] at h
  | succ n ih =>
      intro x w h
      cases x with
      | nil =>
          simp [decodeFlatSententialAux] at h
          subst w
          rfl
      | cons a rest =>
          cases a with
          | terminal a =>
              cases htail : decodeFlatSententialAux n rest with
              | none =>
                  simp [decodeFlatSententialAux, htail] at h
              | some tail =>
                  simp [decodeFlatSententialAux, htail] at h
                  subst w
                  simp [ih rest tail htail]
          | nonterminal A =>
              cases hstack : decodeFlatStack rest with
              | none =>
                  simp [decodeFlatSententialAux, hstack] at h
              | some p =>
                  rcases p with ⟨σ, rest'⟩
                  cases htail : decodeFlatSententialAux n rest' with
                  | none =>
                      simp [decodeFlatSententialAux, hstack, htail] at h
                  | some tail =>
                      simp [decodeFlatSententialAux, hstack, htail] at h
                      subst w
                      have hrest :
                          rest = σ.map FlatSymbol.flag ++ FlatSymbol.stackBottom :: rest' :=
                        encodeFlatStack_of_decodeFlatStack_eq_some hstack
                      have htailEnc : List.flatMap encodeISym tail = rest' := by
                        simpa [encodeSentential] using ih rest' tail htail
                      rw [hrest]
                      simp [encodeSentential, encodeISym, htailEnc, List.append_assoc]
          | flag f =>
              simp [decodeFlatSententialAux] at h
          | stackBottom =>
              simp [decodeFlatSententialAux] at h

theorem decodeFlatSententialAux_encodeSentential_add {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    decodeFlatSententialAux (k + w.length) (encodeSentential w) = some w := by
  induction w generalizing k with
  | nil =>
      cases k <;> rfl
  | cons s w ih =>
      cases s with
      | terminal a =>
          have hfuel :
              k + (ISym.terminal a :: w).length = (k + w.length) + 1 := by
            simp [Nat.add_assoc]
          rw [hfuel]
          simp [decodeFlatSententialAux, encodeSentential]
          rw [show decodeFlatSententialAux (k + w.length) (List.flatMap encodeISym w) =
              some w by
            simpa [encodeSentential] using ih k]
      | indexed A σ =>
          have hfuel :
              k + (ISym.indexed A σ :: w).length = (k + w.length) + 1 := by
            simp [Nat.add_assoc]
          rw [hfuel]
          simp [decodeFlatSententialAux, encodeSentential, encodeISym]
          rw [show decodeFlatSententialAux (k + w.length) (List.flatMap encodeISym w) =
              some w by
            simpa [encodeSentential] using ih k]

@[simp] theorem encodeSentential_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    (encodeSentential w).length =
      w.length + sententialStackHeight w + sententialNonterminalCount w := by
  induction w with
  | nil => simp [encodeSentential, sententialStackHeight, sententialNonterminalCount]
  | cons s w ih =>
      have htail :
          (List.map (fun s => (encodeISym s).length) w).sum =
            w.length + sententialStackHeight w + sententialNonterminalCount w := by
        simpa [encodeSentential] using ih
      cases s with
      | terminal a =>
          simp [encodeSentential, sententialStackHeight, sententialNonterminalCount,
            ISym.stackHeight, ISym.isIndexed, htail]
          omega
      | indexed A σ =>
          simp [encodeSentential, sententialStackHeight, sententialNonterminalCount,
            ISym.stackHeight, ISym.isIndexed, htail]
          omega

@[simp] theorem decodeFlatSentential_encodeSentential {g : IndexedGrammar T}
    (w : List g.ISym) :
    decodeFlatSentential (encodeSentential w) = some w := by
  have h :=
    decodeFlatSententialAux_encodeSentential_add
      (g := g) (sententialStackHeight w + sententialNonterminalCount w) w
  simpa [decodeFlatSentential, encodeSentential_length, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem encodeSentential_of_decodeFlatSentential_eq_some {g : IndexedGrammar T}
    {x : List (FlatSymbol T g.nt g.flag)} {w : List g.ISym}
    (h : decodeFlatSentential x = some w) :
    encodeSentential w = x :=
  encodeSentential_of_decodeFlatSententialAux_eq_some x.length x w h

theorem decodeFlatSentential_eq_some_iff {g : IndexedGrammar T}
    {x : List (FlatSymbol T g.nt g.flag)} {w : List g.ISym} :
    decodeFlatSentential x = some w ↔ x = encodeSentential w := by
  constructor
  · intro h
    exact (encodeSentential_of_decodeFlatSentential_eq_some h).symm
  · intro h
    rw [h]
    simp

@[simp] theorem decodeFlatSentential_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    decodeFlatSentential (g := g)
        (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) =
      some (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have h :=
    decodeFlatSentential_encodeSentential
      (g := g) (w.map fun a => (ISym.terminal a : g.ISym))
  simpa using h

theorem encodeSentential_injective {g : IndexedGrammar T} :
    Function.Injective (encodeSentential (g := g)) := by
  intro u v h
  have hdecode := congrArg (decodeFlatSentential (g := g)) h
  simpa using hdecode

/-- One flat step is an indexed step between the decoded sentential forms. -/
def FlatTransforms (g : IndexedGrammar T)
    (x y : List (FlatSymbol T g.nt g.flag)) : Prop :=
  ∃ w₁ w₂ : List g.ISym,
    decodeFlatSentential x = some w₁ ∧
    decodeFlatSentential y = some w₂ ∧
    g.Transforms w₁ w₂

def FlatDerives (g : IndexedGrammar T) :
    List (FlatSymbol T g.nt g.flag) → List (FlatSymbol T g.nt g.flag) → Prop :=
  Relation.ReflTransGen (FlatTransforms g)

theorem flatTransforms_iff_exists_encoded_transform {g : IndexedGrammar T}
    {x y : List (FlatSymbol T g.nt g.flag)} :
    FlatTransforms g x y ↔
      ∃ w₁ w₂ : List g.ISym,
        x = encodeSentential w₁ ∧ y = encodeSentential w₂ ∧ g.Transforms w₁ w₂ := by
  constructor
  · rintro ⟨w₁, w₂, hx, hy, hstep⟩
    exact ⟨w₁, w₂, (decodeFlatSentential_eq_some_iff.mp hx),
      (decodeFlatSentential_eq_some_iff.mp hy), hstep⟩
  · rintro ⟨w₁, w₂, rfl, rfl, hstep⟩
    exact ⟨w₁, w₂, by simp, by simp, hstep⟩

theorem flatTransforms_encodeSentential_iff {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} :
    FlatTransforms g (encodeSentential w₁) (encodeSentential w₂) ↔
      g.Transforms w₁ w₂ := by
  constructor
  · rintro ⟨u, v, hu, hv, hstep⟩
    have hu_eq : w₁ = u := Option.some.inj (by simpa using hu)
    have hv_eq : w₂ = v := Option.some.inj (by simpa using hv)
    subst u
    subst v
    exact hstep
  · intro hstep
    exact ⟨w₁, w₂, by simp, by simp, hstep⟩

theorem flatDerives_encode_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) :
    FlatDerives g (encodeSentential w₁) (encodeSentential w₂) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (flatTransforms_encodeSentential_iff.mpr hstep)

theorem derives_of_flatDerives_encode_to_decoded {g : IndexedGrammar T}
    {x : List (FlatSymbol T g.nt g.flag)} {w₁ w₂ : List g.ISym}
    (h : FlatDerives g (encodeSentential w₁) x)
    (hx : decodeFlatSentential x = some w₂) :
    g.Derives w₁ w₂ := by
  induction h generalizing w₂ with
  | refl =>
      have hw : w₁ = w₂ := Option.some.inj (by simpa using hx)
      subst w₂
      exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
      rcases hstep with ⟨u, v, hu, hv, hstep⟩
      have hprevDer : g.Derives w₁ u := ih hu
      have hv_eq : v = w₂ := by
        have hs : some v = some w₂ := by
          rw [← hv, hx]
        exact Option.some.inj hs
      subst w₂
      exact hprevDer.tail hstep

theorem flatDerives_encodeSentential_iff {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} :
    FlatDerives g (encodeSentential w₁) (encodeSentential w₂) ↔
      g.Derives w₁ w₂ := by
  constructor
  · intro h
    exact derives_of_flatDerives_encode_to_decoded h (by simp)
  · exact flatDerives_encode_of_derives

theorem flatDerives_initial_terminal_iff_generates {g : IndexedGrammar T}
    {w : List T} :
    FlatDerives g (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ↔
      g.Generates w := by
  rw [← encodeSentential_map_terminal (g := g) w]
  exact flatDerives_encodeSentential_iff

theorem flatDerives_initial_terminal_of_generates {g : IndexedGrammar T}
    {w : List T} (h : g.Generates w) :
    FlatDerives g (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
      (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) :=
  flatDerives_initial_terminal_iff_generates.mpr h

theorem generates_of_flatDerives_initial_terminal {g : IndexedGrammar T}
    {w : List T}
    (h : FlatDerives g
      (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
      (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a))) :
    g.Generates w :=
  flatDerives_initial_terminal_iff_generates.mp h

theorem exists_flatPath_isChain_of_flatDerives {g : IndexedGrammar T}
    {x y : List (FlatSymbol T g.nt g.flag)}
    (h : FlatDerives g x y) :
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? = some x ∧
      path.getLast? = some y ∧
      path.IsChain (FlatTransforms g) := by
  obtain ⟨path, hne, hchain, hhead, hlast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  refine ⟨path, ?_, ?_, hchain⟩
  · rw [List.head?_eq_some_head hne, hhead]
  · rw [List.getLast?_eq_some_getLast hne, hlast]

theorem exists_flatPath_of_flatDerives {g : IndexedGrammar T}
    {x y : List (FlatSymbol T g.nt g.flag)}
    (h : FlatDerives g x y) :
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? = some x ∧
      path.getLast? = some y ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩) := by
  obtain ⟨path, hhead, hlast, hchain⟩ :=
    exists_flatPath_isChain_of_flatDerives h
  refine ⟨path, hhead, hlast, ?_⟩
  rw [List.isChain_iff_getElem] at hchain
  intro i hi
  simpa [List.get_eq_getElem] using hchain i hi

theorem flatDerives_of_flatPath {g : IndexedGrammar T}
    {path : List (List (FlatSymbol T g.nt g.flag))}
    {x y : List (FlatSymbol T g.nt g.flag)}
    (hhead : path.head? = some x)
    (hlast : path.getLast? = some y)
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < path.length,
      FlatTransforms g
        (path.get ⟨i, by omega⟩)
        (path.get ⟨i + 1, hi⟩)) :
    FlatDerives g x y := by
  have hne : path ≠ [] := by
    cases path with
    | nil =>
        simp at hhead
    | cons _ _ =>
        simp
  have hchain : path.IsChain (FlatTransforms g) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simpa [List.get_eq_getElem] using hstep i hi
  have hrt :=
    List.relationReflTransGen_of_exists_isChain path hchain hne
  have hx : path.head hne = x := by
    cases path with
    | nil =>
        contradiction
    | cons a rest =>
        simpa using hhead
  have hy : path.getLast hne = y := by
    have hs : some (path.getLast hne) = some y := by
      rw [← List.getLast?_eq_some_getLast hne, hlast]
    exact Option.some.inj hs
  simpa [FlatDerives, hx, hy] using hrt

theorem generates_of_flatPath_initial_terminal {g : IndexedGrammar T}
    {w : List T} {path : List (List (FlatSymbol T g.nt g.flag))}
    (hhead : path.head? =
      some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)))
    (hlast : path.getLast? =
      some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)))
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < path.length,
      FlatTransforms g
        (path.get ⟨i, by omega⟩)
        (path.get ⟨i + 1, hi⟩)) :
    g.Generates w :=
  generates_of_flatDerives_initial_terminal
    (flatDerives_of_flatPath hhead hlast hstep)

theorem exists_flatPath_initial_terminal_of_generates {g : IndexedGrammar T}
    {w : List T} (h : g.Generates w) :
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      path.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩) := by
  exact exists_flatPath_of_flatDerives
    (flatDerives_initial_terminal_of_generates h)

theorem exists_flatPath_initial_terminal_iff_generates {g : IndexedGrammar T}
    {w : List T} :
    (∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      path.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩)) ↔
      g.Generates w := by
  constructor
  · rintro ⟨path, hhead, hlast, hstep⟩
    exact generates_of_flatPath_initial_terminal hhead hlast hstep
  · exact exists_flatPath_initial_terminal_of_generates

theorem language_eq_exists_flatPath_initial_terminal (g : IndexedGrammar T) :
    g.Language =
      (fun w : List T =>
        ∃ path : List (List (FlatSymbol T g.nt g.flag)),
          path.head? =
            some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
          path.getLast? =
            some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
          ∀ i : ℕ, ∀ hi : i + 1 < path.length,
            FlatTransforms g
              (path.get ⟨i, by omega⟩)
              (path.get ⟨i + 1, hi⟩)) := by
  ext w
  exact exists_flatPath_initial_terminal_iff_generates.symm

@[simp] theorem ISym.isIndexed_terminal {g : IndexedGrammar T} (a : T) :
    ISym.isIndexed (g := g) (ISym.terminal a) = false := rfl

@[simp] theorem ISym.isIndexed_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.isIndexed (g := g) (ISym.indexed A σ) = true := rfl

@[simp] theorem ISym.isTerminal_terminal {g : IndexedGrammar T} (a : T) :
    ISym.isTerminal (g := g) (ISym.terminal a) = true := rfl

@[simp] theorem ISym.isTerminal_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.isTerminal (g := g) (ISym.indexed A σ) = false := rfl

@[simp] theorem ISym.toTerminal?_terminal {g : IndexedGrammar T} (a : T) :
    ISym.toTerminal? (g := g) (ISym.terminal a) = some a := rfl

@[simp] theorem ISym.toTerminal?_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.toTerminal? (g := g) (ISym.indexed A σ) = none := rfl

@[simp] theorem ISym.stackHeight_terminal {g : IndexedGrammar T} (a : T) :
    ISym.stackHeight (g := g) (ISym.terminal a) = 0 := rfl

@[simp] theorem ISym.stackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.stackHeight (g := g) (ISym.indexed A σ) = σ.length := rfl

@[simp] theorem sententialTerminals_nil {g : IndexedGrammar T} :
    sententialTerminals ([] : List g.ISym) = [] := rfl

@[simp] theorem sententialTerminals_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialTerminals (u ++ v) =
      sententialTerminals u ++ sententialTerminals v := by
  simp [sententialTerminals, List.filterMap_append]

@[simp] theorem sententialTerminals_terminal {g : IndexedGrammar T} (a : T) :
    sententialTerminals ([ISym.terminal a] : List g.ISym) = [a] := by
  simp [sententialTerminals]

@[simp] theorem sententialTerminals_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialTerminals ([ISym.indexed A σ] : List g.ISym) = [] := by
  simp [sententialTerminals]

@[simp] theorem sententialTerminals_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialTerminals (ISym.terminal a :: w) = a :: sententialTerminals w := by
  simp [sententialTerminals]

@[simp] theorem sententialTerminals_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialTerminals (ISym.indexed A σ :: w) = sententialTerminals w := by
  simp [sententialTerminals]

@[simp] theorem sententialTerminals_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialTerminals
        (w.map fun a => (ISym.terminal a : g.ISym)) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

@[simp] theorem sententialNonterminalCount_nil {g : IndexedGrammar T} :
    sententialNonterminalCount ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialNonterminalCount_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialNonterminalCount (u ++ v) =
      sententialNonterminalCount u + sententialNonterminalCount v := by
  simp [sententialNonterminalCount, List.countP_append]

@[simp] theorem sententialNonterminalCount_terminal {g : IndexedGrammar T} (a : T) :
    sententialNonterminalCount ([ISym.terminal a] : List g.ISym) = 0 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialNonterminalCount ([ISym.indexed A σ] : List g.ISym) = 1 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialNonterminalCount (ISym.terminal a :: w) =
      sententialNonterminalCount w := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialNonterminalCount (ISym.indexed A σ :: w) =
      sententialNonterminalCount w + 1 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialNonterminalCount
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

theorem sententialNonterminalCount_le_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialNonterminalCount w ≤ w.length := by
  exact List.countP_le_length

@[simp] theorem sententialTerminalCount_nil {g : IndexedGrammar T} :
    sententialTerminalCount ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialTerminalCount_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialTerminalCount (u ++ v) =
      sententialTerminalCount u + sententialTerminalCount v := by
  simp [sententialTerminalCount, List.countP_append]

@[simp] theorem sententialTerminalCount_terminal {g : IndexedGrammar T} (a : T) :
    sententialTerminalCount ([ISym.terminal a] : List g.ISym) = 1 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialTerminalCount ([ISym.indexed A σ] : List g.ISym) = 0 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialTerminalCount (ISym.terminal a :: w) =
      sententialTerminalCount w + 1 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialTerminalCount (ISym.indexed A σ :: w) =
      sententialTerminalCount w := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialTerminalCount
        (w.map fun a => (ISym.terminal a : g.ISym)) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

theorem sententialTerminalCount_le_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialTerminalCount w ≤ w.length := by
  exact List.countP_le_length

@[simp] theorem sententialTerminals_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    (sententialTerminals w).length = sententialTerminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [sententialTerminals, sententialTerminalCount] using ih

theorem sententialTerminalCount_add_nonterminalCount {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialTerminalCount w + sententialNonterminalCount w = w.length := by
  induction w with
  | nil => simp
  | cons s w ih =>
      cases s <;> simp [sententialTerminalCount, sententialNonterminalCount] at ih ⊢ <;> omega

@[simp] theorem sententialStackHeight_nil {g : IndexedGrammar T} :
    sententialStackHeight ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialStackHeight_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialStackHeight (u ++ v) =
      sententialStackHeight u + sententialStackHeight v := by
  simp [sententialStackHeight, List.map_append, List.sum_append]

@[simp] theorem sententialStackHeight_terminal {g : IndexedGrammar T} (a : T) :
    sententialStackHeight ([ISym.terminal a] : List g.ISym) = 0 := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialStackHeight ([ISym.indexed A σ] : List g.ISym) = σ.length := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialStackHeight (ISym.terminal a :: w) =
      sententialStackHeight w := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialStackHeight (ISym.indexed A σ :: w) =
      σ.length + sententialStackHeight w := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialStackHeight
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

@[simp] theorem sententialMaxStackHeight_nil {g : IndexedGrammar T} :
    sententialMaxStackHeight ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialMaxStackHeight_cons {g : IndexedGrammar T}
    (s : g.ISym) (w : List g.ISym) :
    sententialMaxStackHeight (s :: w) =
      max s.stackHeight (sententialMaxStackHeight w) := rfl

@[simp] theorem sententialMaxStackHeight_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialMaxStackHeight (u ++ v) =
      max (sententialMaxStackHeight u) (sententialMaxStackHeight v) := by
  induction u with
  | nil => simp
  | cons s u ih =>
      simp [ih, Nat.max_assoc, Nat.max_comm]

@[simp] theorem sententialMaxStackHeight_terminal {g : IndexedGrammar T} (a : T) :
    sententialMaxStackHeight ([ISym.terminal a] : List g.ISym) = 0 := by
  simp

@[simp] theorem sententialMaxStackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialMaxStackHeight ([ISym.indexed A σ] : List g.ISym) = σ.length := by
  simp

@[simp] theorem sententialMaxStackHeight_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialMaxStackHeight (ISym.terminal a :: w) =
      sententialMaxStackHeight w := by
  simp

@[simp] theorem sententialMaxStackHeight_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialMaxStackHeight (ISym.indexed A σ :: w) =
      max σ.length (sententialMaxStackHeight w) := by
  rfl

@[simp] theorem sententialMaxStackHeight_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialMaxStackHeight
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

/-- A bounded-stack sentential form has a flat encoding whose size is linear in the number of
indexed symbols and terminals. Each terminal takes one cell; each indexed symbol contributes
one nonterminal cell, at most `B` flag cells, and one stack-boundary cell. -/
theorem encodeSentential_length_le_of_maxStackHeight_le {g : IndexedGrammar T}
    {B : ℕ} {w : List g.ISym}
    (hmax : sententialMaxStackHeight w ≤ B) :
    (encodeSentential w).length ≤ w.length * (B + 2) := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          have htail : sententialMaxStackHeight w ≤ B := by
            simpa using hmax
          have htailLen := ih htail
          calc
            (encodeSentential (ISym.terminal a :: w)).length
                = 1 + (encodeSentential w).length := by
                  rw [encodeSentential_cons, List.length_append, encodeISym_length_terminal]
            _ ≤ 1 + w.length * (B + 2) := by omega
            _ ≤ (ISym.terminal a :: w).length * (B + 2) := by
              rw [List.length_cons, Nat.add_mul, Nat.one_mul]
              omega
      | indexed A σ =>
          have hσ : σ.length ≤ B := by
            simpa [sententialMaxStackHeight_cons_indexed] using
              (le_trans (Nat.le_max_left σ.length (sententialMaxStackHeight w)) hmax)
          have htail : sententialMaxStackHeight w ≤ B := by
            simpa [sententialMaxStackHeight_cons_indexed] using
              (le_trans (Nat.le_max_right σ.length (sententialMaxStackHeight w)) hmax)
          have htailLen := ih htail
          calc
            (encodeSentential (ISym.indexed A σ :: w)).length
                = (σ.length + 2) + (encodeSentential w).length := by
                  rw [encodeSentential_cons, List.length_append, encodeISym_length_indexed]
            _ ≤ (B + 2) + w.length * (B + 2) := by omega
            _ = (ISym.indexed A σ :: w).length * (B + 2) := by
              rw [List.length_cons, Nat.add_mul, Nat.one_mul]
              omega

theorem length_take_append_sublist_drop_le {α : Type} {η τ : List α} {P : ℕ}
    (hτ : τ.Sublist (η.drop P)) :
    (η.take P ++ τ).length ≤ η.length := by
  have hτlen : τ.length ≤ (η.drop P).length := hτ.length_le
  rw [List.length_append]
  have hsplit : (η.take P).length + (η.drop P).length = η.length := by
    rw [List.length_take, List.length_drop]
    omega
  omega

theorem sententialMaxStackHeight_context_replace_indexed_le_of_length_le
    {g : IndexedGrammar T} {u v : List g.ISym} {A : g.nt} {σ τ : List g.flag}
    (hτ : τ.length ≤ σ.length) :
    sententialMaxStackHeight (u ++ [ISym.indexed A τ] ++ v) ≤
      sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) := by
  simp only [sententialMaxStackHeight_append, sententialMaxStackHeight_indexed]
  omega

theorem sententialMaxStackHeight_context_replace_indexed_take_append_sublist_drop_le
    {g : IndexedGrammar T} {u v : List g.ISym} {A : g.nt}
    {η τ : List g.flag} {P : ℕ}
    (hτ : τ.Sublist (η.drop P)) :
    sententialMaxStackHeight (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ≤
      sententialMaxStackHeight (u ++ [ISym.indexed A η] ++ v) := by
  apply sententialMaxStackHeight_context_replace_indexed_le_of_length_le
  exact length_take_append_sublist_drop_le hτ

theorem sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le
    {g : IndexedGrammar T} {u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    {B : ℕ}
    (hctx : sententialMaxStackHeight (u ++ v) ≤ B)
    (hσ : σ.length ≤ B) :
    sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) ≤ B := by
  simp only [sententialMaxStackHeight_append, sententialMaxStackHeight_indexed] at *
  omega

theorem sententialMaxStackHeight_context_indexed_take_append_le
    {g : IndexedGrammar T} {u v : List g.ISym} {A : g.nt}
    {η τ : List g.flag} {P K B : ℕ}
    (hctx : sententialMaxStackHeight (u ++ v) ≤ B)
    (hPK : P + K ≤ B)
    (hτ : τ.length ≤ K) :
    sententialMaxStackHeight (u ++ [ISym.indexed A (η.take P ++ τ)] ++ v) ≤ B := by
  apply sententialMaxStackHeight_context_indexed_le_of_context_le_of_stack_le hctx
  rw [List.length_append]
  have htake : (η.take P).length ≤ P := List.length_take_le P η
  omega

theorem stackHeight_le_sententialMaxStackHeight_of_mem {g : IndexedGrammar T}
    {s : g.ISym} {w : List g.ISym} (hs : s ∈ w) :
    s.stackHeight ≤ sententialMaxStackHeight w := by
  induction w with
  | nil => simp at hs
  | cons x w ih =>
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp
      · exact le_trans (ih hs) (by simp)

theorem exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
    {g : IndexedGrammar T} {w : List g.ISym}
    (hpos : 0 < sententialMaxStackHeight w) :
    ∃ A : g.nt, ∃ σ : List g.flag,
      ISym.indexed A σ ∈ w ∧ σ.length = sententialMaxStackHeight w := by
  induction w with
  | nil =>
      simp at hpos
  | cons s w ih =>
      cases s with
      | terminal a =>
          simp only [sententialMaxStackHeight_cons_terminal] at hpos
          obtain ⟨A, σ, hmem, hlen⟩ := ih hpos
          exact ⟨A, σ, List.mem_cons_of_mem _ hmem, hlen⟩
      | indexed A σ =>
          by_cases htail : sententialMaxStackHeight w ≤ σ.length
          · refine ⟨A, σ, List.mem_cons_self, ?_⟩
            rw [sententialMaxStackHeight_cons_indexed, Nat.max_eq_left htail]
          · have hσlt : σ.length < sententialMaxStackHeight w := by omega
            have htail_pos : 0 < sententialMaxStackHeight w := by omega
            obtain ⟨B, τ, hmem, hlen⟩ := ih htail_pos
            refine ⟨B, τ, List.mem_cons_of_mem _ hmem, ?_⟩
            rw [sententialMaxStackHeight_cons_indexed, Nat.max_eq_right (le_of_lt hσlt)]
            exact hlen

theorem exists_indexed_mem_stackHeight_gt_of_sententialMaxStackHeight_gt
    {g : IndexedGrammar T} {w : List g.ISym} {B : ℕ}
    (hgt : B < sententialMaxStackHeight w) :
    ∃ A : g.nt, ∃ σ : List g.flag,
      ISym.indexed A σ ∈ w ∧ B < σ.length := by
  have hpos : 0 < sententialMaxStackHeight w := by omega
  obtain ⟨A, σ, hmem, hlen⟩ :=
    exists_indexed_mem_stackHeight_eq_sententialMaxStackHeight_of_pos
      (g := g) hpos
  exact ⟨A, σ, hmem, by omega⟩

theorem sententialMaxStackHeight_le_sententialStackHeight {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialMaxStackHeight w ≤ sententialStackHeight w := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          simpa using ih
      | indexed A σ =>
          simp
          omega

theorem sententialMaxStackHeight_le_encodeSentential_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialMaxStackHeight w ≤ (encodeSentential w).length := by
  rw [encodeSentential_length]
  exact le_trans (sententialMaxStackHeight_le_sententialStackHeight w) (by omega)

theorem sententialMaxStackHeight_le_of_decodeFlatSentential_eq_some
    {g : IndexedGrammar T} {x : List (FlatSymbol T g.nt g.flag)}
    {w : List g.ISym}
    (h : decodeFlatSentential x = some w) :
    sententialMaxStackHeight w ≤ x.length := by
  calc
    sententialMaxStackHeight w ≤ (encodeSentential w).length :=
      sententialMaxStackHeight_le_encodeSentential_length w
    _ = x.length := by
      exact congrArg List.length (encodeSentential_of_decodeFlatSentential_eq_some h)

theorem sententialStackHeight_le_nonterminalCount_mul_maxStackHeight {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialStackHeight w ≤
      sententialNonterminalCount w * sententialMaxStackHeight w := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          simpa using ih
      | indexed A σ =>
          have htailMax :
              sententialMaxStackHeight w ≤
                max σ.length (sententialMaxStackHeight w) :=
            Nat.le_max_right σ.length (sententialMaxStackHeight w)
          have htail :
              sententialStackHeight w ≤
                sententialNonterminalCount w *
                  max σ.length (sententialMaxStackHeight w) :=
            le_trans ih (Nat.mul_le_mul_left _ htailMax)
          have hσ :
              σ.length ≤ max σ.length (sententialMaxStackHeight w) :=
            Nat.le_max_left σ.length (sententialMaxStackHeight w)
          simp only [sententialStackHeight_cons_indexed,
            sententialNonterminalCount_cons_indexed,
            sententialMaxStackHeight_cons_indexed]
          calc
            σ.length + sententialStackHeight w
                ≤ max σ.length (sententialMaxStackHeight w) +
                    sententialNonterminalCount w *
                      max σ.length (sententialMaxStackHeight w) :=
                  Nat.add_le_add hσ htail
            _ = (sententialNonterminalCount w + 1) *
                    max σ.length (sententialMaxStackHeight w) := by
                  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
    {g : IndexedGrammar T} {B : ℕ} {w : List g.ISym}
    (hmax : sententialMaxStackHeight w ≤ B) :
    sententialStackHeight w ≤ sententialNonterminalCount w * B := by
  exact le_trans
    (sententialStackHeight_le_nonterminalCount_mul_maxStackHeight w)
    (Nat.mul_le_mul_left _ hmax)

theorem encodeSentential_length_le_length_add_nonterminalCount_mul_succ_of_maxStackHeight_le
    {g : IndexedGrammar T} {B : ℕ} {w : List g.ISym}
    (hmax : sententialMaxStackHeight w ≤ B) :
    (encodeSentential w).length ≤ w.length + sententialNonterminalCount w * (B + 1) := by
  rw [encodeSentential_length]
  have hstack :=
    sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
      (g := g) (B := B) (w := w) hmax
  calc
    w.length + sententialStackHeight w + sententialNonterminalCount w
        ≤ w.length + sententialNonterminalCount w * B + sententialNonterminalCount w := by
          omega
    _ = w.length + sententialNonterminalCount w * (B + 1) := by
          rw [Nat.mul_succ]
          omega

/-! ## Stack-suffix extension and sentential measures -/

@[simp] theorem ISym.isIndexed_appendStackSuffix {g : IndexedGrammar T}
    (suffix : List g.flag) (s : g.ISym) :
    (ISym.appendStackSuffix suffix s).isIndexed = s.isIndexed := by
  cases s <;> rfl

@[simp] theorem ISym.isTerminal_appendStackSuffix {g : IndexedGrammar T}
    (suffix : List g.flag) (s : g.ISym) :
    (ISym.appendStackSuffix suffix s).isTerminal = s.isTerminal := by
  cases s <;> rfl

@[simp] theorem ISym.toTerminal?_appendStackSuffix {g : IndexedGrammar T}
    (suffix : List g.flag) (s : g.ISym) :
    (ISym.appendStackSuffix suffix s).toTerminal? = s.toTerminal? := by
  cases s <;> rfl

@[simp] theorem sententialTerminals_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (w : List g.ISym) :
    sententialTerminals (appendStackSuffixes suffix w) = sententialTerminals w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [appendStackSuffixes, sententialTerminals] using ih

@[simp] theorem sententialNonterminalCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (w : List g.ISym) :
    sententialNonterminalCount (appendStackSuffixes suffix w) =
      sententialNonterminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [appendStackSuffixes, sententialNonterminalCount] using ih

@[simp] theorem sententialTerminalCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (w : List g.ISym) :
    sententialTerminalCount (appendStackSuffixes suffix w) =
      sententialTerminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [appendStackSuffixes, sententialTerminalCount] using ih

theorem sententialStackHeight_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (w : List g.ISym) :
    sententialStackHeight (appendStackSuffixes suffix w) =
      sententialStackHeight w + sententialNonterminalCount w * suffix.length := by
  induction w with
  | nil => simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          simpa [appendStackSuffixes, sententialStackHeight, sententialNonterminalCount] using ih
      | indexed A σ =>
          simp only [appendStackSuffixes_cons, ISym.appendStackSuffix_indexed,
            sententialStackHeight_cons_indexed, sententialNonterminalCount_cons_indexed,
            List.length_append]
          rw [ih, Nat.add_mul]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sententialMaxStackHeight_appendStackSuffixes_le {g : IndexedGrammar T}
    (suffix : List g.flag) (w : List g.ISym) :
    sententialMaxStackHeight (appendStackSuffixes suffix w) ≤
      sententialMaxStackHeight w + suffix.length := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s with
      | terminal a =>
          simpa [appendStackSuffixes] using ih
      | indexed A σ =>
          simp only [appendStackSuffixes_cons, ISym.appendStackSuffix_indexed,
            sententialMaxStackHeight_cons, ISym.stackHeight_indexed]
          exact Nat.max_le.mpr
            ⟨by
              rw [List.length_append]
              exact Nat.add_le_add_right
                (Nat.le_max_left σ.length (sententialMaxStackHeight w)) suffix.length,
             le_trans ih
              (Nat.add_le_add_right (Nat.le_max_right σ.length (sententialMaxStackHeight w))
                suffix.length)⟩

/-! ## Stack-prefix projections -/

def ISym.truncateStack {g : IndexedGrammar T} (k : ℕ) : g.ISym → g.ISym
  | ISym.terminal a => ISym.terminal a
  | ISym.indexed A σ => ISym.indexed A (σ.take k)

def truncateStacks {g : IndexedGrammar T} (k : ℕ) (w : List g.ISym) : List g.ISym :=
  w.map (ISym.truncateStack k)

@[simp] theorem ISym.truncateStack_terminal {g : IndexedGrammar T} (k : ℕ) (a : T) :
    ISym.truncateStack (g := g) k (ISym.terminal a) = ISym.terminal a := rfl

@[simp] theorem ISym.truncateStack_indexed {g : IndexedGrammar T} (k : ℕ)
    (A : g.nt) (σ : List g.flag) :
    ISym.truncateStack (g := g) k (ISym.indexed A σ) =
      ISym.indexed A (σ.take k) := rfl

@[simp] theorem truncateStacks_nil {g : IndexedGrammar T} (k : ℕ) :
    truncateStacks (g := g) k [] = [] := rfl

@[simp] theorem truncateStacks_cons {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) (w : List g.ISym) :
    truncateStacks k (s :: w) = ISym.truncateStack k s :: truncateStacks k w := rfl

@[simp] theorem truncateStacks_append {g : IndexedGrammar T} (k : ℕ)
    (u v : List g.ISym) :
    truncateStacks k (u ++ v) = truncateStacks k u ++ truncateStacks k v := by
  simp [truncateStacks, List.map_append]

@[simp] theorem truncateStacks_length {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) :
    (truncateStacks k w).length = w.length := by
  simp [truncateStacks]

@[simp] theorem ISym.isIndexed_truncateStack {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).isIndexed = s.isIndexed := by
  cases s <;> rfl

@[simp] theorem ISym.isTerminal_truncateStack {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).isTerminal = s.isTerminal := by
  cases s <;> rfl

@[simp] theorem ISym.toTerminal?_truncateStack {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).toTerminal? = s.toTerminal? := by
  cases s <;> rfl

@[simp] theorem sententialTerminals_truncateStacks {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialTerminals (truncateStacks k w) = sententialTerminals w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [truncateStacks, sententialTerminals] using ih

@[simp] theorem sententialNonterminalCount_truncateStacks {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialNonterminalCount (truncateStacks k w) =
      sententialNonterminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [truncateStacks, sententialNonterminalCount] using ih

@[simp] theorem sententialTerminalCount_truncateStacks {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialTerminalCount (truncateStacks k w) =
      sententialTerminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [truncateStacks, sententialTerminalCount] using ih

theorem ISym.stackHeight_truncateStack_le_self {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).stackHeight ≤ s.stackHeight := by
  cases s with
  | terminal a => simp
  | indexed A σ => simp [ISym.truncateStack]

theorem ISym.stackHeight_truncateStack_le {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).stackHeight ≤ k := by
  cases s with
  | terminal a => simp
  | indexed A σ => simp [ISym.truncateStack]

theorem ISym.truncateStack_eq_self_of_stackHeight_le {g : IndexedGrammar T}
    {k : ℕ} {s : g.ISym} (h : s.stackHeight ≤ k) :
    ISym.truncateStack k s = s := by
  cases s with
  | terminal a => rfl
  | indexed A σ =>
      simp [ISym.truncateStack, (List.take_eq_self_iff σ).mpr h]

theorem sententialMaxStackHeight_truncateStacks_le_self {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialMaxStackHeight (truncateStacks k w) ≤ sententialMaxStackHeight w := by
  induction w with
  | nil => simp
  | cons s w ih =>
      exact max_le_max (ISym.stackHeight_truncateStack_le_self k s) ih

theorem sententialMaxStackHeight_truncateStacks_le {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialMaxStackHeight (truncateStacks k w) ≤ k := by
  induction w with
  | nil => simp
  | cons s w ih =>
      exact Nat.max_le.mpr ⟨ISym.stackHeight_truncateStack_le k s, ih⟩

theorem truncateStacks_eq_self_of_sententialMaxStackHeight_le {g : IndexedGrammar T}
    {k : ℕ} {w : List g.ISym} (h : sententialMaxStackHeight w ≤ k) :
    truncateStacks k w = w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      have hs : s.stackHeight ≤ k :=
        le_trans (Nat.le_max_left s.stackHeight (sententialMaxStackHeight w)) h
      have hw : sententialMaxStackHeight w ≤ k :=
        le_trans (Nat.le_max_right s.stackHeight (sententialMaxStackHeight w)) h
      rw [truncateStacks_cons, ISym.truncateStack_eq_self_of_stackHeight_le hs, ih hw]

/-! ## Finite bounded sentential forms -/

/-- The finite set of symbols whose attached stack has height at most `n`. -/
def stackBoundedSymbols (g : IndexedGrammar T) (n : ℕ) : Set g.ISym :=
  {s | s.stackHeight ≤ n}

theorem stackBoundedSymbols_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (n : ℕ) :
    (stackBoundedSymbols g n).Finite := by
  classical
  have hterm :
      (Set.range (fun a : T => ISym.terminal (g := g) a) : Set g.ISym).Finite :=
    Set.finite_range _
  have hstacks : ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag n
  have hindexed :
      (⋃ A : g.nt,
        (fun σ : List g.flag => ISym.indexed (g := g) A σ) ''
          ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag))).Finite := by
    apply Set.finite_iUnion
    intro A
    exact hstacks.image fun σ => ISym.indexed (g := g) A σ
  have hcover :
      ((Set.range (fun a : T => ISym.terminal (g := g) a) : Set g.ISym) ∪
        ⋃ A : g.nt,
          (fun σ : List g.flag => ISym.indexed (g := g) A σ) ''
            ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag))).Finite := by
    rw [Set.finite_union]
    exact ⟨hterm, hindexed⟩
  apply hcover.subset
  intro s hs
  cases s with
  | terminal a =>
      exact Or.inl ⟨a, rfl⟩
  | indexed A σ =>
      right
      refine Set.mem_iUnion.mpr ⟨A, ?_⟩
      have hσ : σ.length ≤ n := by
        simpa [stackBoundedSymbols] using hs
      exact ⟨σ, hσ, rfl⟩

/-! ## Finite surface forms -/

/-- A visible indexed-grammar symbol whose stack has been truncated to height at most `k`. -/
def SurfaceSymbol (g : IndexedGrammar T) (k : ℕ) : Type :=
  {s : g.ISym // s.stackHeight ≤ k}

/-- A sentential form over the finite visible stack-prefix alphabet. -/
def SurfaceForm (g : IndexedGrammar T) (k : ℕ) : Type :=
  List (SurfaceSymbol g k)

noncomputable instance SurfaceSymbol.instFintype (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (k : ℕ) :
    Fintype (SurfaceSymbol g k) :=
  (stackBoundedSymbols_finite g k).fintype

noncomputable instance SurfaceSymbol.instDecidableEq (g : IndexedGrammar T) (k : ℕ) :
    DecidableEq (SurfaceSymbol g k) :=
  Classical.decEq _

def surfaceOfTruncatedSymbol {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) : SurfaceSymbol g k :=
  ⟨ISym.truncateStack k s, ISym.stackHeight_truncateStack_le k s⟩

def surfaceOfTruncatedForm {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) : SurfaceForm g k :=
  w.map (surfaceOfTruncatedSymbol k)

def eraseSurfaceSymbol {g : IndexedGrammar T} {k : ℕ}
    (s : SurfaceSymbol g k) : g.ISym :=
  s.1

def eraseSurfaceForm {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) : List g.ISym :=
  w.map eraseSurfaceSymbol

@[simp] theorem surfaceOfTruncatedForm_nil {g : IndexedGrammar T} (k : ℕ) :
    surfaceOfTruncatedForm (g := g) k [] = [] := rfl

@[simp] theorem surfaceOfTruncatedForm_cons {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) (w : List g.ISym) :
    surfaceOfTruncatedForm k (s :: w) =
      surfaceOfTruncatedSymbol k s :: surfaceOfTruncatedForm k w := rfl

@[simp] theorem surfaceOfTruncatedForm_length {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) :
    (surfaceOfTruncatedForm k w).length = w.length := by
  simp [surfaceOfTruncatedForm]

@[simp] theorem eraseSurfaceForm_nil {g : IndexedGrammar T} {k : ℕ} :
    eraseSurfaceForm ([] : SurfaceForm g k) = [] := rfl

@[simp] theorem eraseSurfaceForm_cons {g : IndexedGrammar T} {k : ℕ}
    (s : SurfaceSymbol g k) (w : SurfaceForm g k) :
    eraseSurfaceForm (s :: w) = s.1 :: eraseSurfaceForm w := rfl

@[simp] theorem eraseSurfaceForm_length {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) :
    (eraseSurfaceForm w).length = w.length := by
  simp [eraseSurfaceForm]

@[simp] theorem eraseSurfaceSymbol_surfaceOfTruncatedSymbol {g : IndexedGrammar T}
    (k : ℕ) (s : g.ISym) :
    eraseSurfaceSymbol (surfaceOfTruncatedSymbol k s) = ISym.truncateStack k s := rfl

@[simp] theorem eraseSurfaceForm_surfaceOfTruncatedForm {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    eraseSurfaceForm (surfaceOfTruncatedForm k w) = truncateStacks k w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp [surfaceOfTruncatedForm, eraseSurfaceForm, truncateStacks]

@[simp] theorem sententialTerminals_eraseSurfaceForm_surfaceOfTruncatedForm
    {g : IndexedGrammar T} (k : ℕ) (w : List g.ISym) :
    sententialTerminals (eraseSurfaceForm (surfaceOfTruncatedForm k w)) =
      sententialTerminals w := by
  simp

theorem eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
    {g : IndexedGrammar T} {k : ℕ} {w : List g.ISym}
    (h : sententialMaxStackHeight w ≤ k) :
    eraseSurfaceForm (surfaceOfTruncatedForm k w) = w := by
  rw [eraseSurfaceForm_surfaceOfTruncatedForm,
    truncateStacks_eq_self_of_sententialMaxStackHeight_le h]

theorem eraseSurfaceForm_maxStackHeight_le {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) :
    sententialMaxStackHeight (eraseSurfaceForm w) ≤ k := by
  induction w with
  | nil => simp [eraseSurfaceForm]
  | cons s w ih =>
      exact Nat.max_le.mpr ⟨s.2, ih⟩

/-- Surface forms of bounded length. Their alphabet is already stack-bounded by construction. -/
def boundedSurfaceForms (g : IndexedGrammar T) (lengthBound stackBound : ℕ) :
    Set (SurfaceForm g stackBound) :=
  {w | w.length ≤ lengthBound}

theorem boundedSurfaceForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (lengthBound stackBound : ℕ) :
    (boundedSurfaceForms g lengthBound stackBound).Finite := by
  dsimp [boundedSurfaceForms]
  exact List.finite_length_le (SurfaceSymbol g stackBound) lengthBound

/-- Surface forms bounded by a stack height and compatible with a fixed target word: the
terminal yield already visible in the surface form must occur as a sublist of the target. -/
def targetCompatibleBoundedSurfaceForms (g : IndexedGrammar T)
    (target : List T) (stackBound : ℕ) : Set (SurfaceForm g stackBound) :=
  {w | w ∈ boundedSurfaceForms g target.length stackBound ∧
    (sententialTerminals (eraseSurfaceForm w)).Sublist target}

theorem targetCompatibleBoundedSurfaceForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (target : List T) (stackBound : ℕ) :
    (targetCompatibleBoundedSurfaceForms g target stackBound).Finite := by
  exact (boundedSurfaceForms_finite g target.length stackBound).subset
    (fun _ hw => hw.1)

theorem targetCompatibleBoundedSurfaceForms_subset_boundedSurfaceForms_lengthBound
    {g : IndexedGrammar T} {target : List T} {L stackBound : ℕ}
    (htarget : target.length ≤ L) :
    targetCompatibleBoundedSurfaceForms g target stackBound ⊆
      boundedSurfaceForms g L stackBound := by
  intro surface hsurface
  have hlen : surface.length ≤ target.length := by
    simpa [boundedSurfaceForms] using hsurface.1
  simpa [boundedSurfaceForms] using le_trans hlen htarget

theorem targetCompatibleBoundedSurfaceForms_card_le_boundedSurfaceForms_card_lengthBound
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {target : List T} {L stackBound : ℕ}
    (htarget : target.length ≤ L) :
    (Set.Finite.toFinset
        (targetCompatibleBoundedSurfaceForms_finite g target stackBound)).card ≤
      (Set.Finite.toFinset
        (boundedSurfaceForms_finite g L stackBound)).card := by
  classical
  refine Finset.card_le_card ?_
  intro surface hsurface
  have hsurfaceSet :
      surface ∈ targetCompatibleBoundedSurfaceForms g target stackBound := by
    simpa using hsurface
  have hbounded :=
    targetCompatibleBoundedSurfaceForms_subset_boundedSurfaceForms_lengthBound
      (g := g) (stackBound := stackBound) htarget hsurfaceSet
  simpa using hbounded

theorem surfaceOfTruncatedForm_mem_boundedSurfaceForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : List g.ISym}
    (hlen : w.length ≤ lengthBound) :
    surfaceOfTruncatedForm stackBound w ∈
      boundedSurfaceForms g lengthBound stackBound := by
  simpa [boundedSurfaceForms] using hlen

theorem surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} {target : List T} {stackBound : ℕ}
    {w : List g.ISym}
    (hlen : w.length ≤ target.length)
    (hterm : (sententialTerminals w).Sublist target) :
    surfaceOfTruncatedForm stackBound w ∈
      targetCompatibleBoundedSurfaceForms g target stackBound := by
  exact ⟨surfaceOfTruncatedForm_mem_boundedSurfaceForms hlen, by simpa using hterm⟩

/-- Sentential forms whose length and maximum stack height are both bounded. -/
def boundedSententialForms (g : IndexedGrammar T) (lengthBound stackBound : ℕ) :
    Set (List g.ISym) :=
  {w | w.length ≤ lengthBound ∧ sententialMaxStackHeight w ≤ stackBound}

theorem eraseSurfaceForm_mem_boundedSententialForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : SurfaceForm g stackBound}
    (hw : w ∈ boundedSurfaceForms g lengthBound stackBound) :
    eraseSurfaceForm w ∈ boundedSententialForms g lengthBound stackBound := by
  exact ⟨by simpa [boundedSurfaceForms] using hw,
    eraseSurfaceForm_maxStackHeight_le w⟩

theorem truncateStacks_mem_boundedSententialForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : List g.ISym}
    (hlen : w.length ≤ lengthBound) :
    truncateStacks stackBound w ∈ boundedSententialForms g lengthBound stackBound := by
  exact ⟨by simpa using hlen, sententialMaxStackHeight_truncateStacks_le stackBound w⟩

/-- Flat encoded sentential forms with a bounded tape length. -/
def boundedFlatForms (g : IndexedGrammar T) (flatLengthBound : ℕ) :
    Set (List (FlatSymbol T g.nt g.flag)) :=
  {w | w.length ≤ flatLengthBound}

theorem boundedFlatForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (flatLengthBound : ℕ) :
    (boundedFlatForms g flatLengthBound).Finite := by
  dsimp [boundedFlatForms]
  exact List.finite_length_le (FlatSymbol T g.nt g.flag) flatLengthBound

/-! ## Packing linearly bounded flat forms

The LBA core has only `|w|` tape cells on a nonempty input `w`. A flat sentential form whose
length is bounded by `|w| * W` can still be represented on that tape by storing `W` flat
symbols per cell. The definitions below keep that representation explicit and prove that it
faithfully represents every flat list inside the stated length bound.
-/

/-- A bounded-width block of optional symbols stored in one LBA tape cell. -/
abbrev PackedBlock (α : Type) (W : ℕ) : Type :=
  Fin W → Option α

noncomputable instance PackedBlock.instFintype {α : Type} [Fintype α] (W : ℕ) :
    Fintype (PackedBlock α W) := by
  classical
  change Fintype (Fin W → Option α)
  infer_instance

instance PackedBlock.instDecidableEq {α : Type} [DecidableEq α] (W : ℕ) :
    DecidableEq (PackedBlock α W) := by
  change DecidableEq (Fin W → Option α)
  infer_instance

/-- The `i`-th width-`W` block of a list, padded with `none` past the list end. -/
def packedCell {α : Type} (W : ℕ) (xs : List α) (i : ℕ) : PackedBlock α W :=
  fun j => xs[i * W + j.1]?

/-- Pack a list into `n` width-`W` tape cells. Entries beyond `n * W` are ignored. -/
def packedTape {α : Type} (W n : ℕ) (xs : List α) : Fin n → PackedBlock α W :=
  fun i => packedCell W xs i.1

theorem packedTape_lookup {α : Type} {W n k : ℕ} (xs : List α)
    (hW : 0 < W) (hk : k < n * W) :
    packedTape W n xs
        ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩
        ⟨k % W, Nat.mod_lt k hW⟩ =
      xs[k]? := by
  simp [packedTape, packedCell]
  rw [Nat.mul_comm (k / W) W, Nat.div_add_mod]

theorem packedTape_ext_of_length_le {α : Type} {W n : ℕ} {xs ys : List α}
    (hW : 0 < W) (hxs : xs.length ≤ n * W) (hys : ys.length ≤ n * W)
    (hpack : packedTape W n xs = packedTape W n ys) :
    xs = ys := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n * W
  · have hx := packedTape_lookup (W := W) (n := n) (k := k) xs hW hk
    have hy := packedTape_lookup (W := W) (n := n) (k := k) ys hW hk
    have hp :=
      congrFun
        (congrFun hpack
          ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩)
        ⟨k % W, Nat.mod_lt k hW⟩
    rw [hx, hy] at hp
    exact hp
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- A packed flat form over `n` tape cells, using `W` flat slots per cell. -/
abbrev PackedFlatForm (g : IndexedGrammar T) (W n : ℕ) : Type :=
  Fin n → PackedBlock (FlatSymbol T g.nt g.flag) W

noncomputable instance PackedFlatForm.instFintype (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (W n : ℕ) :
    Fintype (PackedFlatForm g W n) := by
  classical
  change Fintype (Fin n → PackedBlock (FlatSymbol T g.nt g.flag) W)
  infer_instance

noncomputable instance PackedFlatForm.instDecidableEq (g : IndexedGrammar T)
    (W n : ℕ) :
    DecidableEq (PackedFlatForm g W n) :=
  Classical.decEq _

/-- Pack a flat sentential form into `n` width-`W` tape cells. -/
def packedFlatForm (g : IndexedGrammar T) (W n : ℕ)
    (x : List (FlatSymbol T g.nt g.flag)) : PackedFlatForm g W n :=
  packedTape W n x

theorem packedFlatForm_lookup {g : IndexedGrammar T} {W n k : ℕ}
    (x : List (FlatSymbol T g.nt g.flag)) (hW : 0 < W) (hk : k < n * W) :
    packedFlatForm g W n x
        ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩
        ⟨k % W, Nat.mod_lt k hW⟩ =
      x[k]? :=
  packedTape_lookup (W := W) (n := n) (k := k) x hW hk

theorem packedFlatForm_initial_lookup_zero {g : IndexedGrammar T} {W n : ℕ}
    (hW : 0 < W) (hn : 0 < n) :
    packedFlatForm g W n (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        ⟨0, hn⟩ ⟨0, hW⟩ =
      some (FlatSymbol.nonterminal (T := T) (F := g.flag) g.initial) := by
  simp [packedFlatForm, packedTape, packedCell]

theorem packedFlatForm_initial_lookup_one {g : IndexedGrammar T} {W n : ℕ}
    (hW : 1 < W) (hn : 0 < n) :
    packedFlatForm g W n (encodeSentential ([ISym.indexed g.initial []] : List g.ISym))
        ⟨0, hn⟩ ⟨1, hW⟩ =
      some (FlatSymbol.stackBottom (T := T) (N := g.nt) (F := g.flag)) := by
  simp [packedFlatForm, packedTape, packedCell]

theorem packedFlatForm_terminal_lookup {g : IndexedGrammar T} {W n k : ℕ}
    (w : List T) (hW : 0 < W) (hk : k < n * W) :
    packedFlatForm g W n (w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)))
        ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩
        ⟨k % W, Nat.mod_lt k hW⟩ =
      (w[k]?).map (FlatSymbol.terminal (N := g.nt) (F := g.flag)) := by
  rw [packedFlatForm_lookup (g := g) (W := W) (n := n) (k := k)
    (w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag))) hW hk]
  rw [List.getElem?_map]

theorem packedFlatForm_terminal_lookup_of_lt {g : IndexedGrammar T} {W n k : ℕ}
    (w : List T) (hW : 0 < W) (hk : k < n * W) (hkw : k < w.length) :
    packedFlatForm g W n (w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)))
        ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩
        ⟨k % W, Nat.mod_lt k hW⟩ =
      some (FlatSymbol.terminal (N := g.nt) (F := g.flag) (w.get ⟨k, hkw⟩)) := by
  rw [packedFlatForm_terminal_lookup (g := g) (W := W) (n := n) (k := k) w hW hk]
  rw [List.getElem?_eq_getElem hkw]
  rfl

theorem packedFlatForm_ext_of_boundedFlatForms {g : IndexedGrammar T} {W n : ℕ}
    {x y : List (FlatSymbol T g.nt g.flag)}
    (hW : 0 < W) (hx : x ∈ boundedFlatForms g (n * W))
    (hy : y ∈ boundedFlatForms g (n * W))
    (hpack : packedFlatForm g W n x = packedFlatForm g W n y) :
    x = y := by
  exact packedTape_ext_of_length_le (W := W) (n := n) (xs := x) (ys := y) hW
    (by simpa [boundedFlatForms] using hx)
    (by simpa [boundedFlatForms] using hy) hpack

/-- The finite state space of flat sentential forms of length at most `B`. -/
def BoundedFlatForm (g : IndexedGrammar T) (B : ℕ) : Type :=
  {w : List (FlatSymbol T g.nt g.flag) // w ∈ boundedFlatForms g B}

noncomputable instance BoundedFlatForm.instFintype (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (B : ℕ) :
    Fintype (BoundedFlatForm g B) :=
  (boundedFlatForms_finite g B).fintype

noncomputable instance BoundedFlatForm.instDecidableEq (g : IndexedGrammar T) (B : ℕ) :
    DecidableEq (BoundedFlatForm g B) :=
  Classical.decEq _

def packedBoundedFlatForm (g : IndexedGrammar T) (W n : ℕ) :
    BoundedFlatForm g (n * W) → PackedFlatForm g W n :=
  fun x => packedFlatForm g W n x.1

theorem packedBoundedFlatForm_injective {g : IndexedGrammar T} {W n : ℕ}
    (hW : 0 < W) :
    Function.Injective (packedBoundedFlatForm g W n) := by
  intro x y hpack
  apply Subtype.ext
  exact packedFlatForm_ext_of_boundedFlatForms (g := g) (W := W) (n := n) hW
    x.2 y.2 hpack

/-- One flat step restricted to the finite bounded flat-form state space. -/
def BoundedFlatTransforms (g : IndexedGrammar T) (B : ℕ)
    (x y : BoundedFlatForm g B) : Prop :=
  FlatTransforms g x.1 y.1

/-- Reachability in the finite bounded flat-form graph. -/
def BoundedFlatDerives (g : IndexedGrammar T) (B : ℕ) :
    BoundedFlatForm g B → BoundedFlatForm g B → Prop :=
  Relation.ReflTransGen (BoundedFlatTransforms g B)

/-- One bounded-flat step viewed through the packed representation on `n` tape cells
with `W` flat slots per cell. -/
def PackedFlatTransforms (g : IndexedGrammar T) (W n : ℕ)
    (x y : PackedFlatForm g W n) : Prop :=
  ∃ x₀ y₀ : BoundedFlatForm g (n * W),
    x = packedBoundedFlatForm g W n x₀ ∧
    y = packedBoundedFlatForm g W n y₀ ∧
    BoundedFlatTransforms g (n * W) x₀ y₀

/-- Reachability in the packed bounded-flat graph. -/
def PackedFlatDerives (g : IndexedGrammar T) (W n : ℕ) :
    PackedFlatForm g W n → PackedFlatForm g W n → Prop :=
  Relation.ReflTransGen (PackedFlatTransforms g W n)

/-- Exactly `k` steps in the packed bounded-flat graph. -/
def PackedFlatDerivesIn (g : IndexedGrammar T) (W n k : ℕ) :
    PackedFlatForm g W n → PackedFlatForm g W n → Prop :=
  RelDerivesIn (PackedFlatTransforms g W n) k

theorem packedFlatDerives_of_packedFlatDerivesIn
    {g : IndexedGrammar T} {W n k : ℕ} {x y : PackedFlatForm g W n}
    (h : PackedFlatDerivesIn g W n k x y) :
    PackedFlatDerives g W n x y :=
  RelDerivesIn.reflTransGen h

/-- In the finite packed bounded-flat graph, a reachable endpoint pair has a counted
derivation using no more vertices than the whole packed state space. -/
theorem exists_packedFlatDerivesIn_card_bound_of_packedFlatDerives
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {W n : ℕ} {x y : PackedFlatForm g W n}
    (h : PackedFlatDerives g W n x y) :
    ∃ k : ℕ, PackedFlatDerivesIn g W n k x y ∧
      k + 1 ≤ Fintype.card (PackedFlatForm g W n) :=
  RelDerivesIn.exists_card_bound_of_reflTransGen h

/-- Concrete short-path form of packed bounded-flat reachability. -/
theorem exists_packedFlatPath_length_le_card_of_packedFlatDerives
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {W n : ℕ} {x y : PackedFlatForm g W n}
    (h : PackedFlatDerives g W n x y) :
    ∃ path : List (PackedFlatForm g W n),
      path.head? = some x ∧
      path.getLast? = some y ∧
      path.length ≤ Fintype.card (PackedFlatForm g W n) ∧
      path.IsChain (PackedFlatTransforms g W n) := by
  obtain ⟨k, hk, hcard⟩ :=
    exists_packedFlatDerivesIn_card_bound_of_packedFlatDerives
      (g := g) (W := W) (n := n) h
  obtain ⟨path, hlen, hhead, hlast, hchain⟩ := RelDerivesIn.exists_chain hk
  exact ⟨path, hhead, hlast, by simpa [hlen] using hcard, hchain⟩

/-- A concrete packed path gives packed bounded-flat reachability. -/
theorem packedFlatDerives_of_packedFlatPath
    {g : IndexedGrammar T} {W n : ℕ} {x y : PackedFlatForm g W n}
    {path : List (PackedFlatForm g W n)}
    (hhead : path.head? = some x)
    (hlast : path.getLast? = some y)
    (hchain : path.IsChain (PackedFlatTransforms g W n)) :
    PackedFlatDerives g W n x y := by
  have hne : path ≠ [] := by
    cases path with
    | nil =>
        simp at hhead
    | cons _ _ =>
        simp
  have hrt :=
    List.relationReflTransGen_of_exists_isChain path hchain hne
  have hx : path.head hne = x := by
    cases path with
    | nil =>
        contradiction
    | cons a rest =>
        simpa using hhead
  have hy : path.getLast hne = y := by
    have hs : some (path.getLast hne) = some y := by
      rw [← List.getLast?_eq_some_getLast hne, hlast]
    exact Option.some.inj hs
  simpa [PackedFlatDerives, hx, hy] using hrt

theorem packedFlatTransforms_of_boundedFlatTransforms
    {g : IndexedGrammar T} {W n : ℕ}
    {x y : BoundedFlatForm g (n * W)}
    (h : BoundedFlatTransforms g (n * W) x y) :
    PackedFlatTransforms g W n
      (packedBoundedFlatForm g W n x)
      (packedBoundedFlatForm g W n y) :=
  ⟨x, y, rfl, rfl, h⟩

theorem packedFlatTransforms_iff_boundedFlatTransforms
    {g : IndexedGrammar T} {W n : ℕ}
    (hW : 0 < W) {x y : BoundedFlatForm g (n * W)} :
    PackedFlatTransforms g W n
        (packedBoundedFlatForm g W n x)
        (packedBoundedFlatForm g W n y) ↔
      BoundedFlatTransforms g (n * W) x y := by
  constructor
  · rintro ⟨x₀, y₀, hx, hy, hstep⟩
    have hx₀ : x = x₀ := packedBoundedFlatForm_injective (g := g) hW hx
    have hy₀ : y = y₀ := packedBoundedFlatForm_injective (g := g) hW hy
    subst x₀
    subst y₀
    exact hstep
  · exact packedFlatTransforms_of_boundedFlatTransforms

theorem packedFlatDerives_of_boundedFlatDerives
    {g : IndexedGrammar T} {W n : ℕ}
    {x y : BoundedFlatForm g (n * W)}
    (h : BoundedFlatDerives g (n * W) x y) :
    PackedFlatDerives g W n
      (packedBoundedFlatForm g W n x)
      (packedBoundedFlatForm g W n y) := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hab _ ih
    exact Relation.ReflTransGen.head
      (packedFlatTransforms_of_boundedFlatTransforms (g := g) (W := W) (n := n) hab) ih

theorem boundedFlatDerives_of_packedFlatDerives
    {g : IndexedGrammar T} {W n : ℕ} (hW : 0 < W)
    {p q : PackedFlatForm g W n} {x y : BoundedFlatForm g (n * W)}
    (hp : p = packedBoundedFlatForm g W n x)
    (hq : q = packedBoundedFlatForm g W n y)
    (h : PackedFlatDerives g W n p q) :
    BoundedFlatDerives g (n * W) x y := by
  induction h generalizing x y with
  | refl =>
      have hpack : packedBoundedFlatForm g W n x = packedBoundedFlatForm g W n y := by
        rw [← hp, ← hq]
      have hxy : x = y := packedBoundedFlatForm_injective (g := g) hW hpack
      subst y
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      rcases hstep with ⟨u, v, hu, hv, huv⟩
      have hv_y : v = y := by
        apply packedBoundedFlatForm_injective (g := g) hW
        rw [← hv, hq]
      subst v
      have hpre_bounded : BoundedFlatDerives g (n * W) x u :=
        ih hp hu
      exact Relation.ReflTransGen.tail hpre_bounded huv

theorem packedFlatDerives_iff_boundedFlatDerives
    {g : IndexedGrammar T} {W n : ℕ}
    (hW : 0 < W) {x y : BoundedFlatForm g (n * W)} :
    PackedFlatDerives g W n
        (packedBoundedFlatForm g W n x)
        (packedBoundedFlatForm g W n y) ↔
      BoundedFlatDerives g (n * W) x y := by
  constructor
  · exact boundedFlatDerives_of_packedFlatDerives (g := g) (W := W) (n := n) hW rfl rfl
  · exact packedFlatDerives_of_boundedFlatDerives

/-- Exactly `n` bounded flat steps in the finite bounded-flat-form graph. -/
def BoundedFlatDerivesIn (g : IndexedGrammar T) (B : ℕ) (n : ℕ) :
    BoundedFlatForm g B → BoundedFlatForm g B → Prop :=
  RelDerivesIn (BoundedFlatTransforms g B) n

theorem boundedFlatDerives_of_boundedFlatDerivesIn
    {g : IndexedGrammar T} {B n : ℕ} {x y : BoundedFlatForm g B}
    (h : BoundedFlatDerivesIn g B n x y) :
    BoundedFlatDerives g B x y :=
  RelDerivesIn.reflTransGen h

/-- In the finite bounded-flat-form graph, any reachable endpoint pair has a counted
derivation using no more vertices than the whole state space. -/
theorem exists_boundedFlatDerivesIn_card_bound_of_boundedFlatDerives
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {B : ℕ} {x y : BoundedFlatForm g B}
    (h : BoundedFlatDerives g B x y) :
    ∃ n : ℕ, BoundedFlatDerivesIn g B n x y ∧
      n + 1 ≤ Fintype.card (BoundedFlatForm g B) :=
  RelDerivesIn.exists_card_bound_of_reflTransGen h

/-- Concrete path form of
`exists_boundedFlatDerivesIn_card_bound_of_boundedFlatDerives`. -/
theorem exists_boundedFlatPath_length_le_card_of_boundedFlatDerives
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {B : ℕ} {x y : BoundedFlatForm g B}
    (h : BoundedFlatDerives g B x y) :
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? = some x.1 ∧
      path.getLast? = some y.1 ∧
      path.length ≤ Fintype.card (BoundedFlatForm g B) ∧
      (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩) := by
  obtain ⟨n, hn, hcard⟩ :=
    exists_boundedFlatDerivesIn_card_bound_of_boundedFlatDerives
      (g := g) (B := B) h
  obtain ⟨bpath, hlen, hhead, hlast, hchain⟩ := RelDerivesIn.exists_chain hn
  refine ⟨bpath.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, hhead]
    rfl
  · rw [List.getLast?_map, hlast]
    rfl
  · simpa [hlen] using hcard
  · intro i
    have hi : i.1 < bpath.length := by
      simpa using i.2
    rw [List.get_eq_getElem, List.getElem_map]
    exact (bpath.get ⟨i.1, hi⟩).2
  · rw [List.isChain_iff_getElem] at hchain
    intro i hi
    have hi₀ : i + 1 < bpath.length := by
      simpa using hi
    have hrel := hchain i hi₀
    simpa [BoundedFlatTransforms, List.get_eq_getElem] using hrel

theorem boundedFlatDerives_of_boundedFlatPath
    {g : IndexedGrammar T} {B : ℕ} {x y : BoundedFlatForm g B}
    {path : List (List (FlatSymbol T g.nt g.flag))}
    (hhead : path.head? = some x.1)
    (hlast : path.getLast? = some y.1)
    (hbound : ∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B)
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < path.length,
      FlatTransforms g
        (path.get ⟨i, by omega⟩)
        (path.get ⟨i + 1, hi⟩)) :
    BoundedFlatDerives g B x y := by
  induction path generalizing x with
  | nil =>
      simp at hhead
  | cons a rest ih =>
      cases rest with
      | nil =>
          have hx : x.1 = a := by
            simpa using hhead.symm
          have hy : y.1 = a := by
            simpa using hlast.symm
          have hxy : x = y := by
            apply Subtype.ext
            rw [hx, hy]
          subst y
          exact Relation.ReflTransGen.refl
      | cons b rest =>
          have hx : x.1 = a := by
            simpa using hhead.symm
          let z : BoundedFlatForm g B :=
            ⟨b, by
              have hb := hbound ⟨1, by simp⟩
              simpa using hb⟩
          have hfirst : BoundedFlatTransforms g B x z := by
            dsimp [BoundedFlatTransforms, z]
            have h := hstep 0 (by simp)
            simpa [hx] using h
          have htailHead : (b :: rest).head? = some z.1 := by
            simp [z]
          have htailLast : (b :: rest).getLast? = some y.1 := by
            simpa using hlast
          have htailBound :
              ∀ i : Fin (b :: rest).length,
                (b :: rest).get i ∈ boundedFlatForms g B := by
            intro i
            have hiOrig : i.1 + 1 < (a :: b :: rest).length := by
              simpa using Nat.succ_lt_succ i.2
            simpa using hbound ⟨i.1 + 1, hiOrig⟩
          have htailStep :
              ∀ i : ℕ, ∀ hi : i + 1 < (b :: rest).length,
                FlatTransforms g
                  ((b :: rest).get ⟨i, by omega⟩)
                  ((b :: rest).get ⟨i + 1, hi⟩) := by
            intro i hi
            have hiOrig : (i + 1) + 1 < (a :: b :: rest).length := by
              simpa using Nat.succ_lt_succ hi
            simpa using hstep (i + 1) hiOrig
          exact Relation.ReflTransGen.head hfirst
            (ih htailHead htailLast htailBound htailStep)

theorem exists_boundedFlatPath_of_boundedFlatDerives
    {g : IndexedGrammar T} {B : ℕ} {x y : BoundedFlatForm g B}
    (h : BoundedFlatDerives g B x y) :
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? = some x.1 ∧
      path.getLast? = some y.1 ∧
      (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩) := by
  obtain ⟨bpath, hne, hchain, hhead, hlast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  refine ⟨bpath.map Subtype.val, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, List.head?_eq_some_head hne, hhead]
    rfl
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast hne, hlast]
    rfl
  · intro i
    have hi : i.1 < bpath.length := by
      simpa using i.2
    rw [List.get_eq_getElem, List.getElem_map]
    change (bpath[i.1]).1 ∈ boundedFlatForms g B
    exact (bpath.get ⟨i.1, hi⟩).2
  · rw [List.isChain_iff_getElem] at hchain
    intro i hi
    have hi₀ : i + 1 < bpath.length := by
      simpa using hi
    have hrel := hchain i hi₀
    simpa [BoundedFlatTransforms, List.get_eq_getElem] using hrel

theorem exists_list_length_bound {α : Type} (xs : List (List α)) :
    ∃ B : ℕ, ∀ x ∈ xs, x.length ≤ B := by
  induction xs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons x xs ih =>
      rcases ih with ⟨B, hB⟩
      refine ⟨max x.length B, ?_⟩
      intro y hy
      simp at hy
      rcases hy with hxy | hy
      · subst y
        exact Nat.le_max_left x.length B
      · exact le_trans (hB y hy) (Nat.le_max_right x.length B)

theorem encodeSentential_mem_boundedFlatForms_of_length_le_of_maxStackHeight_le
    {g : IndexedGrammar T} {L B : ℕ} {w : List g.ISym}
    (hlen : w.length ≤ L) (hmax : sententialMaxStackHeight w ≤ B) :
    encodeSentential w ∈ boundedFlatForms g (L * (B + 2)) := by
  exact le_trans
    (encodeSentential_length_le_of_maxStackHeight_le hmax)
    (Nat.mul_le_mul_right (B + 2) hlen)

theorem exists_boundedFlatPath_initial_terminal_of_generates {g : IndexedGrammar T}
    {w : List T} (h : g.Generates w) :
    ∃ B : ℕ, ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      path.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩) := by
  obtain ⟨path, hhead, hlast, hstep⟩ :=
    exists_flatPath_initial_terminal_of_generates h
  obtain ⟨B, hB⟩ := exists_list_length_bound path
  refine ⟨B, path, hhead, hlast, ?_, hstep⟩
  intro i
  exact hB (path.get i) (List.get_mem path i)

theorem generates_of_boundedFlatPath_initial_terminal {g : IndexedGrammar T}
    {w : List T} {B : ℕ} {path : List (List (FlatSymbol T g.nt g.flag))}
    (hhead : path.head? =
      some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)))
    (hlast : path.getLast? =
      some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)))
    (_hbound : ∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B)
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < path.length,
      FlatTransforms g
        (path.get ⟨i, by omega⟩)
        (path.get ⟨i + 1, hi⟩)) :
    g.Generates w :=
  generates_of_flatPath_initial_terminal hhead hlast hstep

theorem exists_boundedFlatPath_initial_terminal_iff_generates {g : IndexedGrammar T}
    {w : List T} :
    (∃ B : ℕ, ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      path.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩)) ↔
      g.Generates w := by
  constructor
  · rintro ⟨B, path, hhead, hlast, hbound, hstep⟩
    exact generates_of_boundedFlatPath_initial_terminal hhead hlast hbound hstep
  · exact exists_boundedFlatPath_initial_terminal_of_generates

/-- Words accepted by a flat indexed path whose every flat sentential form has length at
most `B`. This is the fixed finite search slice used by the indexed-to-CS inclusion. -/
def boundedFlatPathLanguage (g : IndexedGrammar T) (B : ℕ) : _root_.Language T :=
  fun w : List T =>
    ∃ path : List (List (FlatSymbol T g.nt g.flag)),
      path.head? =
        some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
      path.getLast? =
        some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
      (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < path.length,
        FlatTransforms g
          (path.get ⟨i, by omega⟩)
          (path.get ⟨i + 1, hi⟩)

theorem boundedFlatPathLanguage_iff_boundedFlatDerives
    {g : IndexedGrammar T} {B : ℕ} {w : List T}
    (hinit :
      encodeSentential ([ISym.indexed g.initial []] : List g.ISym) ∈ boundedFlatForms g B)
    (hterm :
      w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)) ∈ boundedFlatForms g B) :
    w ∈ boundedFlatPathLanguage g B ↔
      BoundedFlatDerives g B
        ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym), hinit⟩
        ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)), hterm⟩ := by
  constructor
  · rintro ⟨path, hhead, hlast, hbound, hstep⟩
    exact boundedFlatDerives_of_boundedFlatPath
      (g := g) (B := B) hhead hlast hbound hstep
  · intro hder
    obtain ⟨path, hhead, hlast, hbound, hstep⟩ :=
      exists_boundedFlatPath_of_boundedFlatDerives (g := g) (B := B) hder
    exact ⟨path, hhead, hlast, hbound, hstep⟩

/-- Finite-search form of `boundedFlatPathLanguage_iff_boundedFlatDerives`: if the initial
and terminal flat forms fit in the fixed bounded-flat state space, membership has a witness
path whose number of nodes is bounded by the cardinality of that state space. -/
theorem boundedFlatPathLanguage_iff_exists_path_length_le_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {B : ℕ} {w : List T}
    (hinit :
      encodeSentential ([ISym.indexed g.initial []] : List g.ISym) ∈ boundedFlatForms g B)
    (hterm :
      w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)) ∈ boundedFlatForms g B) :
    w ∈ boundedFlatPathLanguage g B ↔
      ∃ path : List (List (FlatSymbol T g.nt g.flag)),
        path.head? =
          some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
        path.getLast? =
          some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
        path.length ≤ Fintype.card (BoundedFlatForm g B) ∧
        (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
        ∀ i : ℕ, ∀ hi : i + 1 < path.length,
          FlatTransforms g
            (path.get ⟨i, by omega⟩)
            (path.get ⟨i + 1, hi⟩) := by
  constructor
  · intro hw
    have hder :=
      (boundedFlatPathLanguage_iff_boundedFlatDerives
        (g := g) (B := B) (w := w) hinit hterm).mp hw
    exact exists_boundedFlatPath_length_le_card_of_boundedFlatDerives
      (g := g) (B := B) hder
  · rintro ⟨path, hhead, hlast, _hlen, hbound, hstep⟩
    exact ⟨path, hhead, hlast, hbound, hstep⟩

theorem initial_mem_boundedFlatForms_length_mul_of_pos
    {g : IndexedGrammar T} {B : ℕ} {w : List T} (hwpos : 0 < w.length) :
    encodeSentential ([ISym.indexed g.initial []] : List g.ISym) ∈
      boundedFlatForms g (w.length * (B + 2)) := by
  simp [boundedFlatForms]
  have hw1 : 1 ≤ w.length := Nat.succ_le_of_lt hwpos
  have hB2 : 2 ≤ B + 2 := by omega
  calc
    2 ≤ 1 * (B + 2) := by simp [hB2]
    _ ≤ w.length * (B + 2) := Nat.mul_le_mul_right (B + 2) hw1

theorem terminal_mem_boundedFlatForms_length_mul
    {g : IndexedGrammar T} {B : ℕ} (w : List T) :
    w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)) ∈
      boundedFlatForms g (w.length * (B + 2)) := by
  simp [boundedFlatForms]
  have hfactor : 1 ≤ B + 2 := by omega
  calc
    w.length = w.length * 1 := by rw [Nat.mul_one]
    _ ≤ w.length * (B + 2) := Nat.mul_le_mul_left w.length hfactor

theorem boundedFlatPathLanguage_length_iff_boundedFlatDerives
    {g : IndexedGrammar T} {B : ℕ} {w : List T} (hwne : w ≠ []) :
    w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) ↔
      BoundedFlatDerives g (w.length * (B + 2))
        ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
          initial_mem_boundedFlatForms_length_mul_of_pos
            (g := g) (B := B) (w := w) (List.length_pos_of_ne_nil hwne)⟩
        ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
          terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩ := by
  exact boundedFlatPathLanguage_iff_boundedFlatDerives
    (g := g) (B := w.length * (B + 2)) (w := w)
    (initial_mem_boundedFlatForms_length_mul_of_pos
      (g := g) (B := B) (w := w) (List.length_pos_of_ne_nil hwne))
    (terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w)

theorem boundedFlatPathLanguage_length_iff_packedFlatDerives
    {g : IndexedGrammar T} {B : ℕ} {w : List T} (hwne : w ≠ []) :
    w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) ↔
      PackedFlatDerives g (B + 2) w.length
        (packedBoundedFlatForm g (B + 2) w.length
          ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
            initial_mem_boundedFlatForms_length_mul_of_pos
              (g := g) (B := B) (w := w) (List.length_pos_of_ne_nil hwne)⟩)
        (packedBoundedFlatForm g (B + 2) w.length
          ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
            terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩) := by
  rw [boundedFlatPathLanguage_length_iff_boundedFlatDerives
    (g := g) (B := B) (w := w) hwne]
  exact (packedFlatDerives_iff_boundedFlatDerives (g := g) (W := B + 2)
    (n := w.length) (by omega)).symm

/-- Fixed stack-bound packed flat-path language.

For stack bound `B`, every input word is represented on exactly `|w|` packed tape cells with
`B + 2` flat slots per cell: one nonterminal/terminal slot, up to `B` stack flags, and the
stack-bottom marker. The empty word is excluded because there are no tape cells on which to
place the initial flat sentential form. -/
def packedFlatPathStackBoundLanguage (g : IndexedGrammar T) (B : ℕ) : _root_.Language T :=
  fun w : List T =>
    ∃ hwne : w ≠ [],
      PackedFlatDerives g (B + 2) w.length
        (packedBoundedFlatForm g (B + 2) w.length
          ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
            initial_mem_boundedFlatForms_length_mul_of_pos
              (g := g) (B := B) (w := w) (List.length_pos_of_ne_nil hwne)⟩)
        (packedBoundedFlatForm g (B + 2) w.length
          ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
            terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩)

theorem packedFlatPathStackBoundLanguage_iff_boundedFlatPathLanguage_length
    {g : IndexedGrammar T} {B : ℕ} {w : List T} :
    w ∈ packedFlatPathStackBoundLanguage g B ↔
      w ≠ [] ∧ w ∈ boundedFlatPathLanguage g (w.length * (B + 2)) := by
  constructor
  · rintro ⟨hwne, hpacked⟩
    exact ⟨hwne,
      (boundedFlatPathLanguage_length_iff_packedFlatDerives
        (g := g) (B := B) (w := w) hwne).mpr hpacked⟩
  · rintro ⟨hwne, hflat⟩
    exact ⟨hwne,
      (boundedFlatPathLanguage_length_iff_packedFlatDerives
        (g := g) (B := B) (w := w) hwne).mp hflat⟩

/-- Counted finite-search form of fixed-width packed flat-path membership.

For a fixed packed width `B + 2`, every packed accepting path can be shortened to a counted
path with at most as many vertices as the finite packed state space for the input length. -/
theorem packedFlatPathStackBoundLanguage_iff_exists_packedFlatDerivesIn_card_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {B : ℕ} {w : List T} :
    w ∈ packedFlatPathStackBoundLanguage g B ↔
      ∃ hwne : w ≠ [],
      ∃ k : ℕ,
        PackedFlatDerivesIn g (B + 2) w.length k
          (packedBoundedFlatForm g (B + 2) w.length
            ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
              initial_mem_boundedFlatForms_length_mul_of_pos
                (g := g) (B := B) (w := w)
                (List.length_pos_of_ne_nil hwne)⟩)
          (packedBoundedFlatForm g (B + 2) w.length
            ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
              terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩) ∧
        k + 1 ≤ Fintype.card (PackedFlatForm g (B + 2) w.length) := by
  constructor
  · rintro ⟨hwne, hpacked⟩
    obtain ⟨k, hk, hcard⟩ :=
      exists_packedFlatDerivesIn_card_bound_of_packedFlatDerives
        (g := g) (W := B + 2) (n := w.length) hpacked
    exact ⟨hwne, k, hk, hcard⟩
  · rintro ⟨hwne, k, hk, _hcard⟩
    exact ⟨hwne, packedFlatDerives_of_packedFlatDerivesIn (g := g) hk⟩

/-- Concrete short packed-path form of fixed-width packed flat-path membership.

The witness path lives over exactly `|w|` packed tape cells and has at most as many nodes as
the finite packed state space for that input length. -/
theorem packedFlatPathStackBoundLanguage_iff_exists_packedFlatPath_card_bound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    {B : ℕ} {w : List T} :
    w ∈ packedFlatPathStackBoundLanguage g B ↔
      ∃ hwne : w ≠ [],
      ∃ path : List (PackedFlatForm g (B + 2) w.length),
        path.head? =
          some (packedBoundedFlatForm g (B + 2) w.length
            ⟨encodeSentential ([ISym.indexed g.initial []] : List g.ISym),
              initial_mem_boundedFlatForms_length_mul_of_pos
                (g := g) (B := B) (w := w)
                (List.length_pos_of_ne_nil hwne)⟩) ∧
        path.getLast? =
          some (packedBoundedFlatForm g (B + 2) w.length
            ⟨w.map (FlatSymbol.terminal (N := g.nt) (F := g.flag)),
              terminal_mem_boundedFlatForms_length_mul (g := g) (B := B) w⟩) ∧
        path.length ≤ Fintype.card (PackedFlatForm g (B + 2) w.length) ∧
        path.IsChain (PackedFlatTransforms g (B + 2) w.length) := by
  constructor
  · rintro ⟨hwne, hpacked⟩
    obtain ⟨path, hhead, hlast, hlen, hchain⟩ :=
      exists_packedFlatPath_length_le_card_of_packedFlatDerives
        (g := g) (W := B + 2) (n := w.length) hpacked
    exact ⟨hwne, path, hhead, hlast, hlen, hchain⟩
  · rintro ⟨hwne, path, hhead, hlast, _hlen, hchain⟩
    exact ⟨hwne, packedFlatDerives_of_packedFlatPath
      (g := g) (W := B + 2) (n := w.length)
      (path := path) hhead hlast hchain⟩

theorem nil_not_mem_packedFlatPathStackBoundLanguage
    (g : IndexedGrammar T) (B : ℕ) :
    [] ∉ packedFlatPathStackBoundLanguage g B := by
  intro h
  exact ((packedFlatPathStackBoundLanguage_iff_boundedFlatPathLanguage_length
    (g := g) (B := B) (w := [])).mp h).1 rfl

theorem boundedFlatPathLanguage_subset_language
    {g : IndexedGrammar T} {B : ℕ} {w : List T}
    (h : w ∈ boundedFlatPathLanguage g B) :
    w ∈ g.Language := by
  rcases h with ⟨path, hhead, hlast, hbound, hstep⟩
  exact generates_of_boundedFlatPath_initial_terminal hhead hlast hbound hstep

theorem packedFlatPathStackBoundLanguage_subset_language
    {g : IndexedGrammar T} {B : ℕ} {w : List T}
    (h : w ∈ packedFlatPathStackBoundLanguage g B) :
    w ∈ g.Language := by
  rcases (packedFlatPathStackBoundLanguage_iff_boundedFlatPathLanguage_length
    (g := g) (B := B) (w := w)).mp h with ⟨_hwne, hflat⟩
  exact boundedFlatPathLanguage_subset_language
    (g := g) (B := w.length * (B + 2)) hflat

theorem boundedFlatPathLanguage_mono {g : IndexedGrammar T}
    {B C : ℕ} (hBC : B ≤ C) :
    ∀ w, w ∈ boundedFlatPathLanguage g B →
      w ∈ boundedFlatPathLanguage g C := by
  intro w h
  rcases h with ⟨path, hhead, hlast, hbound, hstep⟩
  refine ⟨path, hhead, hlast, ?_, hstep⟩
  intro i
  have hiB : (path.get i).length ≤ B := by
    simpa [boundedFlatForms] using hbound i
  simpa [boundedFlatForms] using le_trans hiB hBC

theorem language_eq_iUnion_boundedFlatPathLanguage (g : IndexedGrammar T) :
    g.Language = fun w : List T => ∃ B : ℕ, w ∈ boundedFlatPathLanguage g B := by
  ext w
  constructor
  · intro hgen
    obtain ⟨B, path, hhead, hlast, hbound, hstep⟩ :=
      exists_boundedFlatPath_initial_terminal_of_generates (g := g) hgen
    exact ⟨B, path, hhead, hlast, hbound, hstep⟩
  · rintro ⟨B, hB⟩
    exact boundedFlatPathLanguage_subset_language (g := g) (B := B) hB

/-- Each fixed flat-path slice is finite as a language over words: the accepting terminal
flat form is itself one of the bounded nodes, so the accepted word has length at most `B`. -/
theorem finite_boundedFlatPathLanguage [Fintype T]
    (g : IndexedGrammar T) (B : ℕ) :
    ((boundedFlatPathLanguage g B : _root_.Language T) : Set (List T)).Finite := by
  classical
  refine (List.finite_length_le T B).subset ?_
  intro w hw
  rcases hw with ⟨path, _hhead, hlast, hbound, _hstep⟩
  have hlastMem :
      w.map (fun a => FlatSymbol.terminal (N := g.nt) (F := g.flag) a) ∈ path :=
    List.mem_of_getLast? hlast
  rcases List.mem_iff_get.mp hlastMem with ⟨i, hi⟩
  have hflatBound := hbound i
  have hflatLen : (path.get i).length ≤ B := by
    simpa [boundedFlatForms] using hflatBound
  have hlen :
      (w.map fun a => FlatSymbol.terminal (N := g.nt) (F := g.flag) a).length ≤ B := by
    rw [hi] at hflatLen
    simpa using hflatLen
  simpa using hlen

theorem language_eq_exists_boundedFlatPath_initial_terminal (g : IndexedGrammar T) :
    g.Language =
      (fun w : List T =>
        ∃ B : ℕ, ∃ path : List (List (FlatSymbol T g.nt g.flag)),
          path.head? =
            some (encodeSentential ([ISym.indexed g.initial []] : List g.ISym)) ∧
          path.getLast? =
            some (w.map fun a => (FlatSymbol.terminal (N := g.nt) (F := g.flag) a)) ∧
          (∀ i : Fin path.length, path.get i ∈ boundedFlatForms g B) ∧
          ∀ i : ℕ, ∀ hi : i + 1 < path.length,
            FlatTransforms g
              (path.get ⟨i, by omega⟩)
              (path.get ⟨i + 1, hi⟩)) := by
  ext w
  exact exists_boundedFlatPath_initial_terminal_iff_generates.symm

def flatTrace {g : IndexedGrammar T}
    (trace : List (List g.ISym)) : List (List (FlatSymbol T g.nt g.flag)) :=
  trace.map encodeSentential

@[simp] theorem flatTrace_nil {g : IndexedGrammar T} :
    flatTrace ([] : List (List g.ISym)) = [] := rfl

@[simp] theorem flatTrace_cons {g : IndexedGrammar T}
    (w : List g.ISym) (trace : List (List g.ISym)) :
    flatTrace (w :: trace) = encodeSentential w :: flatTrace trace := rfl

@[simp] theorem flatTrace_length {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    (flatTrace trace).length = trace.length := by
  simp [flatTrace]

@[simp] theorem flatTrace_head? {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    (flatTrace trace).head? = trace.head?.map encodeSentential := by
  cases trace <;> rfl

@[simp] theorem flatTrace_getLast? {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    (flatTrace trace).getLast? = trace.getLast?.map encodeSentential := by
  induction trace with
  | nil =>
      rfl
  | cons w trace ih =>
      cases trace with
      | nil =>
          rfl
      | cons w' trace =>
          simpa using ih

theorem flatTrace_get {g : IndexedGrammar T}
    (trace : List (List g.ISym)) {i : ℕ} (hi : i < trace.length) :
    (flatTrace trace).get ⟨i, by simpa using hi⟩ =
      encodeSentential (trace.get ⟨i, hi⟩) := by
  simp [flatTrace]

def surfaceTrace {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) : List (SurfaceForm g stackBound) :=
  trace.map (surfaceOfTruncatedForm stackBound)

@[simp] theorem surfaceTrace_nil {g : IndexedGrammar T} (stackBound : ℕ) :
    surfaceTrace (g := g) stackBound [] = [] := rfl

@[simp] theorem surfaceTrace_cons {g : IndexedGrammar T} (stackBound : ℕ)
    (w : List g.ISym) (trace : List (List g.ISym)) :
    surfaceTrace stackBound (w :: trace) =
      surfaceOfTruncatedForm stackBound w :: surfaceTrace stackBound trace := rfl

@[simp] theorem surfaceTrace_length {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) :
    (surfaceTrace stackBound trace).length = trace.length := by
  simp [surfaceTrace]

theorem surfaceTrace_get {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) {i : ℕ} (hi : i < trace.length) :
    (surfaceTrace stackBound trace).get ⟨i, by simpa using hi⟩ =
      surfaceOfTruncatedForm stackBound (trace.get ⟨i, hi⟩) := by
  simp [surfaceTrace]

theorem boundedSententialForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (lengthBound stackBound : ℕ) :
    (boundedSententialForms g lengthBound stackBound).Finite := by
  classical
  let B := {s : g.ISym // s.stackHeight ≤ stackBound}
  haveI : Fintype B := (stackBoundedSymbols_finite g stackBound).fintype
  let erase : List B → List g.ISym := fun w => w.map Subtype.val
  let boundedLists : Set (List B) := {w | w.length ≤ lengthBound}
  have hboundedLists : boundedLists.Finite := by
    dsimp [boundedLists]
    exact List.finite_length_le B lengthBound
  have himage : (erase '' boundedLists).Finite := hboundedLists.image erase
  apply himage.subset
  intro w hw
  rcases hw with ⟨hlen, hheight⟩
  let lift : List B :=
    w.attach.map fun s =>
      ⟨s.1, le_trans (stackHeight_le_sententialMaxStackHeight_of_mem s.2) hheight⟩
  have hlift_len : lift.length ≤ lengthBound := by
    simpa [lift] using hlen
  have herase : erase lift = w := by
    dsimp [erase, lift]
    rw [List.map_map]
    simp [Function.comp_def]
  exact ⟨lift, hlift_len, herase⟩

/-! ## Counted derivations -/

/-- `DerivesIn g n w₁ w₂` means that `w₁` derives `w₂` in exactly `n` indexed-grammar
steps. This is a counted counterpart to `Derives`, useful when extracting minimal accepting
derivations. -/
def DerivesIn (g : IndexedGrammar T) : ℕ → List g.ISym → List g.ISym → Prop
  | 0, w₁, w₂ => w₁ = w₂
  | n + 1, w₁, w₂ => ∃ w, DerivesIn g n w₁ w ∧ g.Transforms w w₂

@[simp] theorem derivesIn_zero {g : IndexedGrammar T} {w₁ w₂ : List g.ISym} :
    g.DerivesIn 0 w₁ w₂ ↔ w₁ = w₂ :=
  Iff.rfl

@[simp] theorem derivesIn_succ {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} :
    g.DerivesIn (n + 1) w₁ w₂ ↔
      ∃ w, g.DerivesIn n w₁ w ∧ g.Transforms w w₂ :=
  Iff.rfl

theorem derivesIn_refl {g : IndexedGrammar T} (w : List g.ISym) :
    g.DerivesIn 0 w w :=
  rfl

theorem derivesIn_one_of_transforms {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    g.DerivesIn 1 w₁ w₂ :=
  ⟨w₁, rfl, h⟩

theorem derives_of_derivesIn {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    g.Derives w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact g.deri_self w₁
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact (ih hprev).tail hstep

theorem exists_derivesIn_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    ∃ n, g.DerivesIn n w₁ w₂ := by
  induction h with
  | refl =>
      exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, ⟨_, hn, hstep⟩⟩

theorem derives_iff_exists_derivesIn {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} :
    g.Derives w₁ w₂ ↔ ∃ n, g.DerivesIn n w₁ w₂ := by
  constructor
  · exact exists_derivesIn_of_derives
  · rintro ⟨n, h⟩
    exact derives_of_derivesIn h

/-- Any derivation has a propositionally least step count. This avoids requiring decidability
of one-step rewriting. -/
theorem exists_minimal_derivesIn_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    ∃ n, g.DerivesIn n w₁ w₂ ∧
      ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m := by
  obtain ⟨n, hmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (P := fun n => g.DerivesIn n w₁ w₂)
      (exists_derivesIn_of_derives h)
  refine ⟨n, hmin.1, ?_⟩
  intro m hm
  rcases le_total m n with hmn | hnm
  · exact hmin.2 hm hmn
  · exact hnm

theorem derivesIn_trans {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₂ w₃ : List g.ISym}
    (h₁ : g.DerivesIn m w₁ w₂) (h₂ : g.DerivesIn n w₂ w₃) :
    g.DerivesIn (m + n) w₁ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      have hw : w₂ = w₃ := by simpa using h₂
      subst w₃
      simpa using h₁
  | succ n ih =>
      rcases h₂ with ⟨w, hprev, hstep⟩
      exact ⟨w, by simpa [Nat.add_assoc] using ih hprev, hstep⟩

theorem derivesIn_appendStackSuffixes {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂)
    (suffix : List g.flag) :
    g.DerivesIn n (appendStackSuffixes suffix w₁)
      (appendStackSuffixes suffix w₂) := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨appendStackSuffixes suffix w, ih hprev,
        transforms_appendStackSuffixes hstep suffix⟩

theorem derivesIn_appendStackSuffix_indexed {g : IndexedGrammar T} {n : ℕ}
    {A : g.nt} {σ : List g.flag} {w : List g.ISym}
    (h : g.DerivesIn n [ISym.indexed A σ] w)
    (suffix : List g.flag) :
    g.DerivesIn n [ISym.indexed A (σ ++ suffix)]
      (appendStackSuffixes suffix w) := by
  simpa using derivesIn_appendStackSuffixes (g := g) h suffix

theorem derivesIn_appendStackSuffix_to_terminals {g : IndexedGrammar T} {n : ℕ}
    {A : g.nt} {σ : List g.flag} {w : List T}
    (h : g.DerivesIn n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (suffix : List g.flag) :
    g.DerivesIn n [ISym.indexed A (σ ++ suffix)]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using derivesIn_appendStackSuffix_indexed (g := g) h suffix

/-! ## Derivation traces -/

/-- A concrete list of successive sentential forms, each adjacent pair related by one
indexed-grammar step. Length information is carried by the theorems using the trace. -/
def IsDerivationTrace (g : IndexedGrammar T) : List (List g.ISym) → Prop
  | [] => True
  | [_] => True
  | w₁ :: w₂ :: rest => g.Transforms w₁ w₂ ∧ IsDerivationTrace g (w₂ :: rest)

def traceTerminalIncreaseCount {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then 1 else 0) +
        traceTerminalIncreaseCount (w₂ :: rest)
  | _ => 0

def traceNonterminalIncreaseCount {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then 1 else 0) +
        traceNonterminalIncreaseCount (w₂ :: rest)
  | _ => 0

def traceNonterminalDecreaseCount {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 then 1 else 0) +
        traceNonterminalDecreaseCount (w₂ :: rest)
  | _ => 0

def TransformIsObservablePop {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) : Prop :=
  sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∧
    sententialTerminalCount w₂ = sententialTerminalCount w₁ ∧
    sententialStackHeight w₁ = sententialStackHeight w₂ + 1

def traceTerminalIncreaseCountUpTo {g : IndexedGrammar T} :
    ℕ → List (List g.ISym) → ℕ
  | 0, _ => 0
  | i + 1, w₁ :: w₂ :: rest =>
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then 1 else 0) +
        traceTerminalIncreaseCountUpTo i (w₂ :: rest)
  | _ + 1, _ => 0

def traceNonterminalIncreaseCountUpTo {g : IndexedGrammar T} :
    ℕ → List (List g.ISym) → ℕ
  | 0, _ => 0
  | i + 1, w₁ :: w₂ :: rest =>
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then 1 else 0) +
        traceNonterminalIncreaseCountUpTo i (w₂ :: rest)
  | _ + 1, _ => 0

def traceNonterminalDecreaseCountUpTo {g : IndexedGrammar T} :
    ℕ → List (List g.ISym) → ℕ
  | 0, _ => 0
  | i + 1, w₁ :: w₂ :: rest =>
      (if sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 then 1 else 0) +
        traceNonterminalDecreaseCountUpTo i (w₂ :: rest)
  | _ + 1, _ => 0

def TransformIsObservablePush {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) : Prop :=
  sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∧
    sententialTerminalCount w₂ = sententialTerminalCount w₁ ∧
    sententialStackHeight w₂ = sententialStackHeight w₁ + 1

instance instDecidableTransformIsObservablePush {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) : Decidable (TransformIsObservablePush w₁ w₂) := by
  unfold TransformIsObservablePush
  infer_instance

instance instDecidableTransformIsObservablePop {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) : Decidable (TransformIsObservablePop w₁ w₂) := by
  unfold TransformIsObservablePop
  infer_instance

def tracePushStepCount {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if TransformIsObservablePush w₁ w₂ then 1 else 0) +
        tracePushStepCount (w₂ :: rest)
  | _ => 0

def tracePopStepCount {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if TransformIsObservablePop w₁ w₂ then 1 else 0) +
        tracePopStepCount (w₂ :: rest)
  | _ => 0

def traceStackHeightIncrease {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (sententialStackHeight w₂ - sententialStackHeight w₁) +
        traceStackHeightIncrease (w₂ :: rest)
  | _ => 0

def traceStackHeightDecrease {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (sententialStackHeight w₁ - sententialStackHeight w₂) +
        traceStackHeightDecrease (w₂ :: rest)
  | _ => 0

def traceBinaryCopyStackHeight {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then
        sententialStackHeight w₂ - sententialStackHeight w₁
      else
        0) + traceBinaryCopyStackHeight (w₂ :: rest)
  | _ => 0

def traceTerminalEraseStackHeight {g : IndexedGrammar T} :
    List (List g.ISym) → ℕ
  | w₁ :: w₂ :: rest =>
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then
        sententialStackHeight w₁ - sententialStackHeight w₂
      else
        0) + traceTerminalEraseStackHeight (w₂ :: rest)
  | _ => 0

def tracePushStepCountUpTo {g : IndexedGrammar T} :
    ℕ → List (List g.ISym) → ℕ
  | 0, _ => 0
  | i + 1, w₁ :: w₂ :: rest =>
      (if TransformIsObservablePush w₁ w₂ then 1 else 0) +
        tracePushStepCountUpTo i (w₂ :: rest)
  | _ + 1, _ => 0

def tracePopStepCountUpTo {g : IndexedGrammar T} :
    ℕ → List (List g.ISym) → ℕ
  | 0, _ => 0
  | i + 1, w₁ :: w₂ :: rest =>
      (if TransformIsObservablePop w₁ w₂ then 1 else 0) +
        tracePopStepCountUpTo i (w₂ :: rest)
  | _ + 1, _ => 0

@[simp] theorem isDerivationTrace_nil {g : IndexedGrammar T} :
    IsDerivationTrace g [] := by
  simp [IsDerivationTrace]

@[simp] theorem isDerivationTrace_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    IsDerivationTrace g [w] := by
  simp [IsDerivationTrace]

@[simp] theorem isDerivationTrace_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    IsDerivationTrace g (w₁ :: w₂ :: rest) ↔
      g.Transforms w₁ w₂ ∧ IsDerivationTrace g (w₂ :: rest) := by
  rfl

theorem isDerivationTrace_appendStackSuffixes {g : IndexedGrammar T}
    {trace : List (List g.ISym)} (htrace : IsDerivationTrace g trace)
    (suffix : List g.flag) :
    IsDerivationTrace g (trace.map (appendStackSuffixes suffix)) := by
  induction trace with
  | nil =>
      simp
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          simp
      | cons w₂ rest =>
          simp only [isDerivationTrace_cons_cons] at htrace ⊢
          exact ⟨transforms_appendStackSuffixes htrace.1 suffix, ih htrace.2⟩

@[simp] theorem traceTerminalIncreaseCount_nil {g : IndexedGrammar T} :
    traceTerminalIncreaseCount ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceTerminalIncreaseCount_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceTerminalIncreaseCount [w] = 0 := rfl

@[simp] theorem traceTerminalIncreaseCount_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceTerminalIncreaseCount (w₁ :: w₂ :: rest) =
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then 1 else 0) +
        traceTerminalIncreaseCount (w₂ :: rest) := rfl

@[simp] theorem traceNonterminalIncreaseCount_nil {g : IndexedGrammar T} :
    traceNonterminalIncreaseCount ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceNonterminalIncreaseCount_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceNonterminalIncreaseCount [w] = 0 := rfl

@[simp] theorem traceNonterminalIncreaseCount_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceNonterminalIncreaseCount (w₁ :: w₂ :: rest) =
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then 1 else 0) +
        traceNonterminalIncreaseCount (w₂ :: rest) := rfl

@[simp] theorem traceNonterminalDecreaseCount_nil {g : IndexedGrammar T} :
    traceNonterminalDecreaseCount ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceNonterminalDecreaseCount_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceNonterminalDecreaseCount [w] = 0 := rfl

@[simp] theorem traceNonterminalDecreaseCount_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceNonterminalDecreaseCount (w₁ :: w₂ :: rest) =
      (if sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 then 1 else 0) +
        traceNonterminalDecreaseCount (w₂ :: rest) := rfl

@[simp] theorem tracePushStepCount_nil {g : IndexedGrammar T} :
    tracePushStepCount ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem tracePushStepCount_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    tracePushStepCount [w] = 0 := rfl

@[simp] theorem tracePushStepCount_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    tracePushStepCount (w₁ :: w₂ :: rest) =
      (if TransformIsObservablePush w₁ w₂ then 1 else 0) +
        tracePushStepCount (w₂ :: rest) := rfl

@[simp] theorem tracePopStepCount_nil {g : IndexedGrammar T} :
    tracePopStepCount ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem tracePopStepCount_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    tracePopStepCount [w] = 0 := rfl

@[simp] theorem tracePopStepCount_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    tracePopStepCount (w₁ :: w₂ :: rest) =
      (if TransformIsObservablePop w₁ w₂ then 1 else 0) +
        tracePopStepCount (w₂ :: rest) := rfl

@[simp] theorem traceStackHeightIncrease_nil {g : IndexedGrammar T} :
    traceStackHeightIncrease ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceStackHeightIncrease_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceStackHeightIncrease [w] = 0 := rfl

@[simp] theorem traceStackHeightIncrease_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceStackHeightIncrease (w₁ :: w₂ :: rest) =
      (sententialStackHeight w₂ - sententialStackHeight w₁) +
        traceStackHeightIncrease (w₂ :: rest) := rfl

@[simp] theorem traceStackHeightDecrease_nil {g : IndexedGrammar T} :
    traceStackHeightDecrease ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceStackHeightDecrease_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceStackHeightDecrease [w] = 0 := rfl

@[simp] theorem traceStackHeightDecrease_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceStackHeightDecrease (w₁ :: w₂ :: rest) =
      (sententialStackHeight w₁ - sententialStackHeight w₂) +
        traceStackHeightDecrease (w₂ :: rest) := rfl

@[simp] theorem traceBinaryCopyStackHeight_nil {g : IndexedGrammar T} :
    traceBinaryCopyStackHeight ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceBinaryCopyStackHeight_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceBinaryCopyStackHeight [w] = 0 := rfl

@[simp] theorem traceBinaryCopyStackHeight_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceBinaryCopyStackHeight (w₁ :: w₂ :: rest) =
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then
        sententialStackHeight w₂ - sententialStackHeight w₁
      else
        0) + traceBinaryCopyStackHeight (w₂ :: rest) := rfl

@[simp] theorem traceTerminalEraseStackHeight_nil {g : IndexedGrammar T} :
    traceTerminalEraseStackHeight ([] : List (List g.ISym)) = 0 := rfl

@[simp] theorem traceTerminalEraseStackHeight_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    traceTerminalEraseStackHeight [w] = 0 := rfl

@[simp] theorem traceTerminalEraseStackHeight_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceTerminalEraseStackHeight (w₁ :: w₂ :: rest) =
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then
        sententialStackHeight w₁ - sententialStackHeight w₂
      else
        0) + traceTerminalEraseStackHeight (w₂ :: rest) := rfl

theorem traceStackHeight_balance {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {first last : List g.ISym}
    (hhead : trace.head? = some first)
    (hlast : trace.getLast? = some last) :
    sententialStackHeight last + traceStackHeightDecrease trace =
      sententialStackHeight first + traceStackHeightIncrease trace := by
  induction trace generalizing first last with
  | nil =>
      simp at hhead
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hhead hlast
          subst first
          subst last
          simp
      | cons b rest =>
          have hfirst : a = first := by simpa using hhead
          subst first
          have ih_tail :
              sententialStackHeight last +
                  traceStackHeightDecrease (b :: rest) =
                sententialStackHeight b +
                  traceStackHeightIncrease (b :: rest) :=
            ih (first := b) (last := last) (by simp) (by simpa using hlast)
          simp only [traceStackHeightDecrease_cons_cons,
            traceStackHeightIncrease_cons_cons]
          omega

theorem accepting_derivationTrace_stackHeightIncrease_eq_decrease
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {w : List T}
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceStackHeightIncrease trace = traceStackHeightDecrease trace := by
  have hbalance := traceStackHeight_balance (g := g) hhead hlast
  simpa using hbalance.symm

theorem trace_drop_head?_eq_get {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {i : ℕ} (hi : i < trace.length) :
    (trace.drop i).head? = some (trace.get ⟨i, hi⟩) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem trace_drop_getLast?_eq_getLast? {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {i : ℕ} (hi : i < trace.length) :
    (trace.drop i).getLast? = trace.getLast? := by
  have hdrop_ne : trace.drop i ≠ [] := by
    intro hnil
    have hhead := trace_drop_head?_eq_get (g := g) hi
    rw [hnil] at hhead
    simp at hhead
  have hlast :=
    List.getLast?_append_of_ne_nil (trace.take i) (l₂ := trace.drop i) hdrop_ne
  rw [List.take_append_drop] at hlast
  exact hlast.symm

theorem isDerivationTrace_drop {g : IndexedGrammar T}
    {trace : List (List g.ISym)} (htrace : IsDerivationTrace g trace)
    (i : ℕ) :
    IsDerivationTrace g (trace.drop i) := by
  induction i generalizing trace with
  | zero =>
      simpa using htrace
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ rest =>
          cases rest with
          | nil =>
              simp
          | cons w₂ rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              simpa using ih htrace.2

theorem trace_get_stackHeight_le_last_add_drop_decrease
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {last : List g.ISym} {i : ℕ}
    (hi : i < trace.length)
    (hlast : trace.getLast? = some last) :
    sententialStackHeight (trace.get ⟨i, hi⟩) ≤
      sententialStackHeight last + traceStackHeightDecrease (trace.drop i) := by
  have hhead := trace_drop_head?_eq_get (g := g) hi
  have hlast_drop : (trace.drop i).getLast? = some last := by
    rw [trace_drop_getLast?_eq_getLast? (g := g) hi, hlast]
  have hbalance :=
    traceStackHeight_balance (g := g) hhead hlast_drop
  omega

theorem accepting_derivationTrace_get_stackHeight_le_future_decrease
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {w : List T}
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialStackHeight (trace.get ⟨i, hi⟩) ≤
      traceStackHeightDecrease (trace.drop i) := by
  have h :=
    trace_get_stackHeight_le_last_add_drop_decrease
      (g := g) (last := w.map ISym.terminal) hi hlast
  simpa using h

theorem accepting_derivationTrace_get_maxStackHeight_le_future_decrease
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {w : List T}
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      traceStackHeightDecrease (trace.drop i) := by
  exact le_trans (sententialMaxStackHeight_le_sententialStackHeight _)
    (accepting_derivationTrace_get_stackHeight_le_future_decrease
      (g := g) hlast hi)

@[simp] theorem traceTerminalIncreaseCountUpTo_zero {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    traceTerminalIncreaseCountUpTo 0 trace = 0 := rfl

@[simp] theorem traceTerminalIncreaseCountUpTo_nil {g : IndexedGrammar T}
    (i : ℕ) :
    traceTerminalIncreaseCountUpTo i ([] : List (List g.ISym)) = 0 := by
  cases i <;> rfl

@[simp] theorem traceTerminalIncreaseCountUpTo_singleton {g : IndexedGrammar T}
    (i : ℕ) (w : List g.ISym) :
    traceTerminalIncreaseCountUpTo i [w] = 0 := by
  cases i <;> rfl

@[simp] theorem traceTerminalIncreaseCountUpTo_succ_cons_cons {g : IndexedGrammar T}
    (i : ℕ) (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceTerminalIncreaseCountUpTo (i + 1) (w₁ :: w₂ :: rest) =
      (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then 1 else 0) +
        traceTerminalIncreaseCountUpTo i (w₂ :: rest) := rfl

@[simp] theorem traceNonterminalIncreaseCountUpTo_zero {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    traceNonterminalIncreaseCountUpTo 0 trace = 0 := rfl

@[simp] theorem traceNonterminalIncreaseCountUpTo_nil {g : IndexedGrammar T}
    (i : ℕ) :
    traceNonterminalIncreaseCountUpTo i ([] : List (List g.ISym)) = 0 := by
  cases i <;> rfl

@[simp] theorem traceNonterminalIncreaseCountUpTo_singleton {g : IndexedGrammar T}
    (i : ℕ) (w : List g.ISym) :
    traceNonterminalIncreaseCountUpTo i [w] = 0 := by
  cases i <;> rfl

@[simp] theorem traceNonterminalIncreaseCountUpTo_succ_cons_cons {g : IndexedGrammar T}
    (i : ℕ) (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceNonterminalIncreaseCountUpTo (i + 1) (w₁ :: w₂ :: rest) =
      (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then 1 else 0) +
        traceNonterminalIncreaseCountUpTo i (w₂ :: rest) := rfl

@[simp] theorem traceNonterminalDecreaseCountUpTo_zero {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    traceNonterminalDecreaseCountUpTo 0 trace = 0 := rfl

@[simp] theorem traceNonterminalDecreaseCountUpTo_nil {g : IndexedGrammar T}
    (i : ℕ) :
    traceNonterminalDecreaseCountUpTo i ([] : List (List g.ISym)) = 0 := by
  cases i <;> rfl

@[simp] theorem traceNonterminalDecreaseCountUpTo_singleton {g : IndexedGrammar T}
    (i : ℕ) (w : List g.ISym) :
    traceNonterminalDecreaseCountUpTo i [w] = 0 := by
  cases i <;> rfl

@[simp] theorem traceNonterminalDecreaseCountUpTo_succ_cons_cons {g : IndexedGrammar T}
    (i : ℕ) (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    traceNonterminalDecreaseCountUpTo (i + 1) (w₁ :: w₂ :: rest) =
      (if sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 then 1 else 0) +
        traceNonterminalDecreaseCountUpTo i (w₂ :: rest) := rfl

@[simp] theorem tracePushStepCountUpTo_zero {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    tracePushStepCountUpTo 0 trace = 0 := rfl

@[simp] theorem tracePushStepCountUpTo_nil {g : IndexedGrammar T}
    (i : ℕ) :
    tracePushStepCountUpTo i ([] : List (List g.ISym)) = 0 := by
  cases i <;> rfl

@[simp] theorem tracePushStepCountUpTo_singleton {g : IndexedGrammar T}
    (i : ℕ) (w : List g.ISym) :
    tracePushStepCountUpTo i [w] = 0 := by
  cases i <;> rfl

@[simp] theorem tracePushStepCountUpTo_succ_cons_cons {g : IndexedGrammar T}
    (i : ℕ) (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    tracePushStepCountUpTo (i + 1) (w₁ :: w₂ :: rest) =
      (if TransformIsObservablePush w₁ w₂ then 1 else 0) +
        tracePushStepCountUpTo i (w₂ :: rest) := rfl

@[simp] theorem tracePopStepCountUpTo_zero {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    tracePopStepCountUpTo 0 trace = 0 := rfl

@[simp] theorem tracePopStepCountUpTo_nil {g : IndexedGrammar T}
    (i : ℕ) :
    tracePopStepCountUpTo i ([] : List (List g.ISym)) = 0 := by
  cases i <;> rfl

@[simp] theorem tracePopStepCountUpTo_singleton {g : IndexedGrammar T}
    (i : ℕ) (w : List g.ISym) :
    tracePopStepCountUpTo i [w] = 0 := by
  cases i <;> rfl

@[simp] theorem tracePopStepCountUpTo_succ_cons_cons {g : IndexedGrammar T}
    (i : ℕ) (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    tracePopStepCountUpTo (i + 1) (w₁ :: w₂ :: rest) =
      (if TransformIsObservablePop w₁ w₂ then 1 else 0) +
        tracePopStepCountUpTo i (w₂ :: rest) := rfl

theorem TransformIsObservablePush_appendStackSuffixes_iff {g : IndexedGrammar T}
    (suffix : List g.flag) (w₁ w₂ : List g.ISym) :
    TransformIsObservablePush (appendStackSuffixes suffix w₁)
        (appendStackSuffixes suffix w₂) ↔
      TransformIsObservablePush w₁ w₂ := by
  unfold TransformIsObservablePush
  constructor
  · rintro ⟨hnt, hterm, hstack⟩
    simp only [sententialNonterminalCount_appendStackSuffixes,
      sententialTerminalCount_appendStackSuffixes] at hnt hterm
    rw [sententialStackHeight_appendStackSuffixes,
      sententialStackHeight_appendStackSuffixes] at hstack
    rw [hnt] at hstack
    exact ⟨hnt, hterm, by omega⟩
  · rintro ⟨hnt, hterm, hstack⟩
    simp only [sententialNonterminalCount_appendStackSuffixes,
      sententialTerminalCount_appendStackSuffixes]
    refine ⟨hnt, hterm, ?_⟩
    rw [sententialStackHeight_appendStackSuffixes,
      sententialStackHeight_appendStackSuffixes, hnt]
    omega

theorem TransformIsObservablePop_appendStackSuffixes_iff {g : IndexedGrammar T}
    (suffix : List g.flag) (w₁ w₂ : List g.ISym) :
    TransformIsObservablePop (appendStackSuffixes suffix w₁)
        (appendStackSuffixes suffix w₂) ↔
      TransformIsObservablePop w₁ w₂ := by
  unfold TransformIsObservablePop
  constructor
  · rintro ⟨hnt, hterm, hstack⟩
    simp only [sententialNonterminalCount_appendStackSuffixes,
      sententialTerminalCount_appendStackSuffixes] at hnt hterm
    rw [sententialStackHeight_appendStackSuffixes,
      sententialStackHeight_appendStackSuffixes] at hstack
    rw [hnt] at hstack
    exact ⟨hnt, hterm, by omega⟩
  · rintro ⟨hnt, hterm, hstack⟩
    simp only [sententialNonterminalCount_appendStackSuffixes,
      sententialTerminalCount_appendStackSuffixes]
    refine ⟨hnt, hterm, ?_⟩
    rw [sententialStackHeight_appendStackSuffixes,
      sententialStackHeight_appendStackSuffixes, hnt]
    omega

theorem traceTerminalIncreaseCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (trace : List (List g.ISym)) :
    traceTerminalIncreaseCount (trace.map (appendStackSuffixes suffix)) =
      traceTerminalIncreaseCount trace := by
  induction trace with
  | nil =>
      rfl
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          rfl
      | cons w₂ rest =>
          have htail :
              traceTerminalIncreaseCount
                  (appendStackSuffixes suffix w₂ ::
                    List.map (appendStackSuffixes suffix) rest) =
                traceTerminalIncreaseCount (w₂ :: rest) := by
            simpa using ih
          simp only [List.map_cons, traceTerminalIncreaseCount_cons_cons,
            sententialTerminalCount_appendStackSuffixes]
          rw [htail]

theorem traceNonterminalIncreaseCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (trace : List (List g.ISym)) :
    traceNonterminalIncreaseCount (trace.map (appendStackSuffixes suffix)) =
      traceNonterminalIncreaseCount trace := by
  induction trace with
  | nil =>
      rfl
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          rfl
      | cons w₂ rest =>
          have htail :
              traceNonterminalIncreaseCount
                  (appendStackSuffixes suffix w₂ ::
                    List.map (appendStackSuffixes suffix) rest) =
                traceNonterminalIncreaseCount (w₂ :: rest) := by
            simpa using ih
          simp only [List.map_cons, traceNonterminalIncreaseCount_cons_cons,
            sententialNonterminalCount_appendStackSuffixes]
          rw [htail]

theorem traceNonterminalDecreaseCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (trace : List (List g.ISym)) :
    traceNonterminalDecreaseCount (trace.map (appendStackSuffixes suffix)) =
      traceNonterminalDecreaseCount trace := by
  induction trace with
  | nil =>
      rfl
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          rfl
      | cons w₂ rest =>
          have htail :
              traceNonterminalDecreaseCount
                  (appendStackSuffixes suffix w₂ ::
                    List.map (appendStackSuffixes suffix) rest) =
                traceNonterminalDecreaseCount (w₂ :: rest) := by
            simpa using ih
          simp only [List.map_cons, traceNonterminalDecreaseCount_cons_cons,
            sententialNonterminalCount_appendStackSuffixes]
          rw [htail]

theorem tracePushStepCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (trace : List (List g.ISym)) :
    tracePushStepCount (trace.map (appendStackSuffixes suffix)) =
      tracePushStepCount trace := by
  induction trace with
  | nil =>
      rfl
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          rfl
      | cons w₂ rest =>
          have htail :
              tracePushStepCount
                  (appendStackSuffixes suffix w₂ ::
                    List.map (appendStackSuffixes suffix) rest) =
                tracePushStepCount (w₂ :: rest) := by
            simpa using ih
          have hiff := TransformIsObservablePush_appendStackSuffixes_iff
            (g := g) suffix w₁ w₂
          by_cases hpush : TransformIsObservablePush w₁ w₂
          · have hpush' :
                TransformIsObservablePush (appendStackSuffixes suffix w₁)
                  (appendStackSuffixes suffix w₂) := hiff.mpr hpush
            simp only [List.map_cons, tracePushStepCount_cons_cons, if_pos hpush',
              if_pos hpush]
            rw [htail]
          · have hpush' :
                ¬ TransformIsObservablePush (appendStackSuffixes suffix w₁)
                  (appendStackSuffixes suffix w₂) := by
              intro h
              exact hpush (hiff.mp h)
            simp only [List.map_cons, tracePushStepCount_cons_cons, if_neg hpush',
              if_neg hpush, zero_add]
            rw [htail]

theorem tracePopStepCount_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (trace : List (List g.ISym)) :
    tracePopStepCount (trace.map (appendStackSuffixes suffix)) =
      tracePopStepCount trace := by
  induction trace with
  | nil =>
      rfl
  | cons w₁ rest ih =>
      cases rest with
      | nil =>
          rfl
      | cons w₂ rest =>
          have htail :
              tracePopStepCount
                  (appendStackSuffixes suffix w₂ ::
                    List.map (appendStackSuffixes suffix) rest) =
                tracePopStepCount (w₂ :: rest) := by
            simpa using ih
          have hiff := TransformIsObservablePop_appendStackSuffixes_iff
            (g := g) suffix w₁ w₂
          by_cases hpop : TransformIsObservablePop w₁ w₂
          · have hpop' :
                TransformIsObservablePop (appendStackSuffixes suffix w₁)
                  (appendStackSuffixes suffix w₂) := hiff.mpr hpop
            simp only [List.map_cons, tracePopStepCount_cons_cons, if_pos hpop',
              if_pos hpop]
            rw [htail]
          · have hpop' :
                ¬ TransformIsObservablePop (appendStackSuffixes suffix w₁)
                  (appendStackSuffixes suffix w₂) := by
              intro h
              exact hpop (hiff.mp h)
            simp only [List.map_cons, tracePopStepCount_cons_cons, if_neg hpop',
              if_neg hpop, zero_add]
            rw [htail]

theorem traceTerminalIncreaseCountUpTo_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (i : ℕ) (trace : List (List g.ISym)) :
    traceTerminalIncreaseCountUpTo i (trace.map (appendStackSuffixes suffix)) =
      traceTerminalIncreaseCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      rfl
  | succ i ih =>
      cases trace with
      | nil =>
          rfl
      | cons w₁ rest =>
          cases rest with
          | nil =>
              rfl
          | cons w₂ rest =>
              have htail :
                  traceTerminalIncreaseCountUpTo i
                      (appendStackSuffixes suffix w₂ ::
                        List.map (appendStackSuffixes suffix) rest) =
                    traceTerminalIncreaseCountUpTo i (w₂ :: rest) := by
                simpa using ih (w₂ :: rest)
              simp only [List.map_cons, traceTerminalIncreaseCountUpTo_succ_cons_cons,
                sententialTerminalCount_appendStackSuffixes]
              rw [htail]

theorem traceNonterminalIncreaseCountUpTo_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (i : ℕ) (trace : List (List g.ISym)) :
    traceNonterminalIncreaseCountUpTo i (trace.map (appendStackSuffixes suffix)) =
      traceNonterminalIncreaseCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      rfl
  | succ i ih =>
      cases trace with
      | nil =>
          rfl
      | cons w₁ rest =>
          cases rest with
          | nil =>
              rfl
          | cons w₂ rest =>
              have htail :
                  traceNonterminalIncreaseCountUpTo i
                      (appendStackSuffixes suffix w₂ ::
                        List.map (appendStackSuffixes suffix) rest) =
                    traceNonterminalIncreaseCountUpTo i (w₂ :: rest) := by
                simpa using ih (w₂ :: rest)
              simp only [List.map_cons, traceNonterminalIncreaseCountUpTo_succ_cons_cons,
                sententialNonterminalCount_appendStackSuffixes]
              rw [htail]

theorem traceNonterminalDecreaseCountUpTo_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (i : ℕ) (trace : List (List g.ISym)) :
    traceNonterminalDecreaseCountUpTo i (trace.map (appendStackSuffixes suffix)) =
      traceNonterminalDecreaseCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      rfl
  | succ i ih =>
      cases trace with
      | nil =>
          rfl
      | cons w₁ rest =>
          cases rest with
          | nil =>
              rfl
          | cons w₂ rest =>
              have htail :
                  traceNonterminalDecreaseCountUpTo i
                      (appendStackSuffixes suffix w₂ ::
                        List.map (appendStackSuffixes suffix) rest) =
                    traceNonterminalDecreaseCountUpTo i (w₂ :: rest) := by
                simpa using ih (w₂ :: rest)
              simp only [List.map_cons, traceNonterminalDecreaseCountUpTo_succ_cons_cons,
                sententialNonterminalCount_appendStackSuffixes]
              rw [htail]

theorem tracePushStepCountUpTo_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (i : ℕ) (trace : List (List g.ISym)) :
    tracePushStepCountUpTo i (trace.map (appendStackSuffixes suffix)) =
      tracePushStepCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      rfl
  | succ i ih =>
      cases trace with
      | nil =>
          rfl
      | cons w₁ rest =>
          cases rest with
          | nil =>
              rfl
          | cons w₂ rest =>
              have htail :
                  tracePushStepCountUpTo i
                      (appendStackSuffixes suffix w₂ ::
                        List.map (appendStackSuffixes suffix) rest) =
                    tracePushStepCountUpTo i (w₂ :: rest) := by
                simpa using ih (w₂ :: rest)
              have hiff := TransformIsObservablePush_appendStackSuffixes_iff
                (g := g) suffix w₁ w₂
              by_cases hpush : TransformIsObservablePush w₁ w₂
              · have hpush' :
                    TransformIsObservablePush (appendStackSuffixes suffix w₁)
                      (appendStackSuffixes suffix w₂) := hiff.mpr hpush
                simp only [List.map_cons, tracePushStepCountUpTo_succ_cons_cons,
                  if_pos hpush', if_pos hpush]
                rw [htail]
              · have hpush' :
                    ¬ TransformIsObservablePush (appendStackSuffixes suffix w₁)
                      (appendStackSuffixes suffix w₂) := by
                  intro h
                  exact hpush (hiff.mp h)
                simp only [List.map_cons, tracePushStepCountUpTo_succ_cons_cons,
                  if_neg hpush', if_neg hpush, zero_add]
                rw [htail]

theorem tracePopStepCountUpTo_appendStackSuffixes {g : IndexedGrammar T}
    (suffix : List g.flag) (i : ℕ) (trace : List (List g.ISym)) :
    tracePopStepCountUpTo i (trace.map (appendStackSuffixes suffix)) =
      tracePopStepCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      rfl
  | succ i ih =>
      cases trace with
      | nil =>
          rfl
      | cons w₁ rest =>
          cases rest with
          | nil =>
              rfl
          | cons w₂ rest =>
              have htail :
                  tracePopStepCountUpTo i
                      (appendStackSuffixes suffix w₂ ::
                        List.map (appendStackSuffixes suffix) rest) =
                    tracePopStepCountUpTo i (w₂ :: rest) := by
                simpa using ih (w₂ :: rest)
              have hiff := TransformIsObservablePop_appendStackSuffixes_iff
                (g := g) suffix w₁ w₂
              by_cases hpop : TransformIsObservablePop w₁ w₂
              · have hpop' :
                    TransformIsObservablePop (appendStackSuffixes suffix w₁)
                      (appendStackSuffixes suffix w₂) := hiff.mpr hpop
                simp only [List.map_cons, tracePopStepCountUpTo_succ_cons_cons,
                  if_pos hpop', if_pos hpop]
                rw [htail]
              · have hpop' :
                    ¬ TransformIsObservablePop (appendStackSuffixes suffix w₁)
                      (appendStackSuffixes suffix w₂) := by
                  intro h
                  exact hpop (hiff.mp h)
                simp only [List.map_cons, tracePopStepCountUpTo_succ_cons_cons,
                  if_neg hpop', if_neg hpop, zero_add]
                rw [htail]

theorem traceTerminalIncreaseCountUpTo_le_traceTerminalIncreaseCount
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    traceTerminalIncreaseCountUpTo i trace ≤ traceTerminalIncreaseCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              simpa using Nat.add_le_add_left (ih (w₂ :: rest))
                (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then 1 else 0)

theorem traceNonterminalIncreaseCountUpTo_le_traceNonterminalIncreaseCount
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    traceNonterminalIncreaseCountUpTo i trace ≤ traceNonterminalIncreaseCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              simpa using Nat.add_le_add_left (ih (w₂ :: rest))
                (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then 1 else 0)

theorem traceNonterminalDecreaseCountUpTo_le_traceNonterminalDecreaseCount
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    traceNonterminalDecreaseCountUpTo i trace ≤ traceNonterminalDecreaseCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              simpa using Nat.add_le_add_left (ih (w₂ :: rest))
                (if sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 then 1 else 0)

theorem tracePushStepCountUpTo_le_tracePushStepCount
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    tracePushStepCountUpTo i trace ≤ tracePushStepCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              simpa using Nat.add_le_add_left (ih (w₂ :: rest))
                (if TransformIsObservablePush w₁ w₂ then 1 else 0)

theorem tracePopStepCountUpTo_le_tracePopStepCount
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    tracePopStepCountUpTo i trace ≤ tracePopStepCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              simpa using Nat.add_le_add_left (ih (w₂ :: rest))
                (if TransformIsObservablePop w₁ w₂ then 1 else 0)

theorem tracePopStepCount_drop_le
    {g : IndexedGrammar T} (i : ℕ) (trace : List (List g.ISym)) :
    tracePopStepCount (trace.drop i) ≤ tracePopStepCount trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              have htail := ih (w₂ :: rest)
              by_cases hpop : TransformIsObservablePop w₁ w₂
              · simp [tracePopStepCount, hpop]
                omega
              · simp [tracePopStepCount, hpop]
                omega

theorem tracePopStepCount_le_length_sub_one
    {g : IndexedGrammar T} (trace : List (List g.ISym)) :
    tracePopStepCount trace ≤ trace.length - 1 := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          have htail : tracePopStepCount (w₂ :: rest) ≤ rest.length := by
            simpa using ih
          by_cases hpop : TransformIsObservablePop w₁ w₂
          · simp [tracePopStepCount, hpop]
            omega
          · simp [tracePopStepCount, hpop]
            omega

theorem tracePopStepCount_le_steps_of_length_eq
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {n : ℕ}
    (hlen : trace.length = n + 1) :
    tracePopStepCount trace ≤ n := by
  have h := tracePopStepCount_le_length_sub_one (g := g) trace
  omega

theorem tracePushStepCount_le_traceStackHeightIncrease
    {g : IndexedGrammar T} (trace : List (List g.ISym)) :
    tracePushStepCount trace ≤ traceStackHeightIncrease trace := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          by_cases hpush : TransformIsObservablePush w₁ w₂
          · have hpush' := hpush
            rcases hpush with ⟨_, _, hstack⟩
            have hdelta :
                sententialStackHeight w₂ - sententialStackHeight w₁ = 1 := by
              omega
            simp [hpush', hdelta]
            omega
          · simp [hpush]
            omega

theorem tracePopStepCount_le_traceStackHeightDecrease
    {g : IndexedGrammar T} (trace : List (List g.ISym)) :
    tracePopStepCount trace ≤ traceStackHeightDecrease trace := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          by_cases hpop : TransformIsObservablePop w₁ w₂
          · have hpop' := hpop
            rcases hpop with ⟨_, _, hstack⟩
            have hdelta :
                sententialStackHeight w₁ - sententialStackHeight w₂ = 1 := by
              omega
            simp [hpop', hdelta]
            omega
          · simp [hpop]
            omega

theorem accepting_derivationTrace_pushStepCount_le_stackHeightDecrease
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {w : List T}
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    tracePushStepCount trace ≤ traceStackHeightDecrease trace := by
  have hpush := tracePushStepCount_le_traceStackHeightIncrease (g := g) trace
  have hbalance :=
    accepting_derivationTrace_stackHeightIncrease_eq_decrease (g := g) hhead hlast
  omega

theorem accepting_derivationTrace_popStepCount_le_stackHeightIncrease
    {g : IndexedGrammar T} {trace : List (List g.ISym)} {w : List T}
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    tracePopStepCount trace ≤ traceStackHeightIncrease trace := by
  have hpop := tracePopStepCount_le_traceStackHeightDecrease (g := g) trace
  have hbalance :=
    accepting_derivationTrace_stackHeightIncrease_eq_decrease (g := g) hhead hlast
  omega

theorem tracePushStepCountUpTo_le_index {g : IndexedGrammar T}
    (i : ℕ) (trace : List (List g.ISym)) :
    tracePushStepCountUpTo i trace ≤ i := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              have htail := ih (w₂ :: rest)
              by_cases hpush : TransformIsObservablePush w₁ w₂
              · simp [hpush]
                omega
              · simp [hpush]
                omega

theorem tracePopStepCountUpTo_le_index {g : IndexedGrammar T}
    (i : ℕ) (trace : List (List g.ISym)) :
    tracePopStepCountUpTo i trace ≤ i := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons w₁ trace =>
          cases trace with
          | nil =>
              simp
          | cons w₂ rest =>
              have htail := ih (w₂ :: rest)
              by_cases hpop : TransformIsObservablePop w₁ w₂
              · simp [hpop]
                omega
              · simp [hpop]
                omega

theorem isDerivationTrace_append_step {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w w' : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some w)
    (hstep : g.Transforms w w') :
    IsDerivationTrace g (trace ++ [w']) := by
  induction trace with
  | nil =>
      simp at hlast
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hlast
          subst a
          simp [hstep]
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace ⊢
          constructor
          · exact htrace.1
          · exact ih htrace.2 (by simpa using hlast)

theorem exists_isDerivationTrace_of_derivesIn {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    ∃ trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some w₁ ∧ trace.getLast? = some w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact ⟨[w₁], by simp⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      rcases ih hprev with ⟨trace, htrace, hlen, hhead, hlast⟩
      refine ⟨trace ++ [w₂], ?_, ?_, ?_, ?_⟩
      · exact isDerivationTrace_append_step htrace hlast hstep
      · simp [hlen]
      · rw [List.head?_append]
        simp [hhead]
      · simp

theorem derivesIn_of_isDerivationTrace {g : IndexedGrammar T} {n : ℕ}
    {trace : List (List g.ISym)} {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂) :
    g.DerivesIn n w₁ w₂ := by
  induction n generalizing trace w₁ w₂ with
  | zero =>
      cases trace with
      | nil => simp at hlen
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hhead hlast
              subst a
              simpa using hlast
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
              have htail : g.DerivesIn n b w₂ :=
                ih htrace.2 hlen_tail (by simp) hlast_tail
              have hone : g.DerivesIn 1 w₁ b :=
                derivesIn_one_of_transforms htrace.1
              simpa [Nat.add_comm] using derivesIn_trans hone htail

theorem derivesIn_iff_exists_isDerivationTrace {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} :
    g.DerivesIn n w₁ w₂ ↔
      ∃ trace,
        IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
          trace.head? = some w₁ ∧ trace.getLast? = some w₂ := by
  constructor
  · exact exists_isDerivationTrace_of_derivesIn
  · rintro ⟨trace, htrace, hlen, hhead, hlast⟩
    exact derivesIn_of_isDerivationTrace htrace hlen hhead hlast

theorem flatDerives_encode_of_isDerivationTrace_head_last {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂) :
    FlatDerives g (encodeSentential w₁) (encodeSentential w₂) := by
  let n := trace.length - 1
  have hlen_pos : 0 < trace.length := by
    cases trace with
    | nil =>
        simp at hhead
    | cons _ _ =>
        simp
  have hlen : trace.length = n + 1 := by
    dsimp [n]
    omega
  exact flatDerives_encode_of_derives
    (derives_of_derivesIn
      (derivesIn_of_isDerivationTrace (g := g) htrace hlen hhead hlast))

/-- Adjacent entries in a derivation trace are related by one grammar step. -/
theorem isDerivationTrace_get_transform {g : IndexedGrammar T}
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) {i : ℕ}
    (hi : i + 1 < trace.length) :
    g.Transforms
      (trace.get ⟨i, by omega⟩)
      (trace.get ⟨i + 1, hi⟩) := by
  induction trace generalizing i with
  | nil =>
      simp at hi
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hi
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          cases i with
          | zero =>
              simpa using htrace.1
          | succ i =>
              have hi_tail : i + 1 < (b :: rest).length := by
                simpa using hi
              simpa using ih htrace.2 hi_tail

theorem flatTrace_get_flatTransforms_of_isDerivationTrace {g : IndexedGrammar T}
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) {i : ℕ}
    (hi : i + 1 < (flatTrace trace).length) :
    FlatTransforms g
      ((flatTrace trace).get ⟨i, by omega⟩)
      ((flatTrace trace).get ⟨i + 1, hi⟩) := by
  have hiTrace : i + 1 < trace.length := by
    simpa using hi
  have hi0 : i < trace.length := by omega
  rw [flatTrace_get trace hi0, flatTrace_get trace hiTrace]
  exact flatTransforms_encodeSentential_iff.mpr
    (isDerivationTrace_get_transform htrace hiTrace)

theorem isDerivationTrace_derivesIn_from_head_get {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w₁ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some w₁) {i : ℕ}
    (hi : i < trace.length) :
    g.DerivesIn i w₁ (trace.get ⟨i, hi⟩) := by
  induction i with
  | zero =>
      cases trace with
      | nil => simp at hi
      | cons a rest =>
          simp at hhead
          subst a
          rfl
  | succ i ih =>
      have hi_prev : i < trace.length := by omega
      have hprev := ih hi_prev
      have hstep := isDerivationTrace_get_transform htrace (i := i) hi
      exact ⟨trace.get ⟨i, hi_prev⟩, hprev, hstep⟩

theorem isDerivationTrace_derivesIn_get_to_last {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some w₂) {i : ℕ}
    (hi : i < trace.length) :
    g.DerivesIn (trace.length - 1 - i) (trace.get ⟨i, hi⟩) w₂ := by
  induction trace generalizing i with
  | nil =>
      simp at hi
  | cons a rest ih =>
      cases rest with
      | nil =>
          have hi0 : i = 0 := by simpa using hi
          subst i
          simp at hlast
          subst a
          rfl
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          cases i with
          | zero =>
              have htrace_full : IsDerivationTrace g (a :: b :: rest) := by
                simpa only [isDerivationTrace_cons_cons] using htrace
              exact derivesIn_of_isDerivationTrace htrace_full
                (by simp)
                (by simp)
                hlast
          | succ i =>
              have hi_tail : i < (b :: rest).length := by
                simpa using hi
              have htail := ih htrace.2 hlast hi_tail
              simpa using htail

/-- Counted derivability between two displayed positions of a derivation trace. -/
theorem isDerivationTrace_derivesIn_get_to_get {g : IndexedGrammar T}
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) {i j : ℕ}
    (hi : i < trace.length) (hj : j < trace.length) (hij : i ≤ j) :
    g.DerivesIn (j - i) (trace.get ⟨i, hi⟩) (trace.get ⟨j, hj⟩) := by
  have hdropTrace : IsDerivationTrace g (trace.drop i) :=
    isDerivationTrace_drop htrace i
  have hdropHead :
      (trace.drop i).head? = some (trace.get ⟨i, hi⟩) :=
    trace_drop_head?_eq_get (g := g) hi
  have hdropIdx : j - i < (trace.drop i).length := by
    rw [List.length_drop]
    omega
  have hdropGet :
      (trace.drop i).get ⟨j - i, hdropIdx⟩ = trace.get ⟨j, hj⟩ := by
    simp only [List.get_eq_getElem, List.getElem_drop, Nat.add_sub_of_le hij]
  have hder :=
    isDerivationTrace_derivesIn_from_head_get
      (g := g) hdropTrace hdropHead hdropIdx
  rwa [hdropGet] at hder

/-- Split a counted derivation after `m` steps. -/
theorem derivesIn_split {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₃ : List g.ISym}
    (h : g.DerivesIn (m + n) w₁ w₃) :
    ∃ w₂, g.DerivesIn m w₁ w₂ ∧ g.DerivesIn n w₂ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      exact ⟨w₃, by simpa using h, rfl⟩
  | succ n ih =>
      rcases (show g.DerivesIn ((m + n) + 1) w₁ w₃ by
        simpa [Nat.add_assoc] using h) with ⟨w, hprev, hstep⟩
      rcases ih hprev with ⟨w₂, hm, hn⟩
      exact ⟨w₂, hm, ⟨w, hn, hstep⟩⟩

/-- Split a counted derivation at any index `i ≤ n`. -/
theorem derivesIn_split_at {g : IndexedGrammar T} {n i : ℕ}
    {w₁ w₂ : List g.ISym} (hi : i ≤ n)
    (h : g.DerivesIn n w₁ w₂) :
    ∃ x, g.DerivesIn i w₁ x ∧ g.DerivesIn (n - i) x w₂ := by
  have h' : g.DerivesIn (i + (n - i)) w₁ w₂ := by
    simpa [Nat.add_sub_of_le hi] using h
  exact derivesIn_split (g := g) (m := i) (n := n - i) h'

/-- `x` is the sentential form seen at step `i` of an `n`-step derivation from `w₁` to
`w₂`. -/
def DerivesInIntermediate (g : IndexedGrammar T) (n : ℕ)
    (w₁ w₂ : List g.ISym) (i : ℕ) (x : List g.ISym) : Prop :=
  i ≤ n ∧ g.DerivesIn i w₁ x ∧ g.DerivesIn (n - i) x w₂

theorem exists_derivesInIntermediate {g : IndexedGrammar T} {n i : ℕ}
    {w₁ w₂ : List g.ISym} (hi : i ≤ n)
    (h : g.DerivesIn n w₁ w₂) :
    ∃ x, DerivesInIntermediate g n w₁ w₂ i x := by
  rcases derivesIn_split_at (g := g) hi h with ⟨x, hpre, hsuf⟩
  exact ⟨x, hi, hpre, hsuf⟩

theorem derivesInIntermediate_appendStackSuffixes {g : IndexedGrammar T}
    {n i : ℕ} {w₁ w₂ x : List g.ISym}
    (hmid : DerivesInIntermediate g n w₁ w₂ i x)
    (suffix : List g.flag) :
    DerivesInIntermediate g n
      (appendStackSuffixes suffix w₁) (appendStackSuffixes suffix w₂) i
      (appendStackSuffixes suffix x) := by
  exact ⟨hmid.1, derivesIn_appendStackSuffixes hmid.2.1 suffix,
    derivesIn_appendStackSuffixes hmid.2.2 suffix⟩

theorem derivesInIntermediate_appendStackSuffix_to_terminals {g : IndexedGrammar T}
    {n i : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)) i x)
    (suffix : List g.flag) :
    DerivesInIntermediate g n [ISym.indexed A (σ ++ suffix)]
      (w.map fun a => (ISym.terminal a : g.ISym)) i
      (appendStackSuffixes suffix x) := by
  simpa using derivesInIntermediate_appendStackSuffixes (g := g) hmid suffix

/-- A shortest counted derivation cannot see the same intermediate sentential form at two
different step indices. -/
theorem minimal_derivesIn_intermediate_index_eq {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ x : List g.ISym}
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m)
    {i j : ℕ}
    (hi : DerivesInIntermediate g n w₁ w₂ i x)
    (hj : DerivesInIntermediate g n w₁ w₂ j x) :
    i = j := by
  rcases hi with ⟨hin, hpre_i, hsuf_i⟩
  rcases hj with ⟨hjn, hpre_j, hsuf_j⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hshort : g.DerivesIn (i + (n - j)) w₁ w₂ :=
      derivesIn_trans hpre_i hsuf_j
    have hshort_lt : i + (n - j) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)
  · rfl
  · have hshort : g.DerivesIn (j + (n - i)) w₁ w₂ :=
      derivesIn_trans hpre_j hsuf_i
    have hshort_lt : j + (n - i) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)

theorem isDerivationTrace_get_intermediate {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {n i : ℕ}
    {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂)
    (hi : i ≤ n) :
    DerivesInIntermediate g n w₁ w₂ i
      (trace.get ⟨i, by omega⟩) := by
  have hi_len : i < trace.length := by omega
  refine ⟨hi, ?_, ?_⟩
  · simpa using isDerivationTrace_derivesIn_from_head_get htrace hhead hi_len
  · have hsuf := isDerivationTrace_derivesIn_get_to_last htrace hlast hi_len
    simpa [hlen] using hsuf

theorem minimal_derivationTrace_nodup {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {n : ℕ} {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂)
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m) :
    trace.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  intro i j hij hsame
  have hi_le : i.1 ≤ n := by
    have hi_len := i.2
    omega
  have hj_le : j.1 ≤ n := by
    have hj_len := j.2
    omega
  have hmid_i :=
    isDerivationTrace_get_intermediate (g := g) htrace hlen hhead hlast hi_le
  have hmid_j :
      DerivesInIntermediate g n w₁ w₂ j.1 (trace.get i) := by
    have hmid_j0 :=
      isDerivationTrace_get_intermediate (g := g) htrace hlen hhead hlast hj_le
    convert hmid_j0 using 1
  have hij_eq : i.1 = j.1 :=
    minimal_derivesIn_intermediate_index_eq (g := g) (n := n) hmin hmid_i hmid_j
  exact (ne_of_lt hij) (Fin.ext hij_eq)

/-- A duplicate-free list whose entries all lie in a finite set has length bounded by the
cardinality of that set. This formulation avoids requiring decidable equality on the ambient
type. -/
theorem List.Nodup.length_le_finite_set_card_of_get_mem {α : Type}
    {xs : List α} (hxs : xs.Nodup) (S : Set α) (hS : S.Finite)
    (hmem : ∀ i : Fin xs.length, xs.get i ∈ S) :
    xs.length ≤ (Set.Finite.toFinset hS).card := by
  classical
  haveI : Fintype S := hS.fintype
  let f : Fin xs.length → S := fun i => ⟨xs.get i, hmem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hget : xs.get i = xs.get j := congrArg Subtype.val hij
    exact (List.Nodup.get_inj_iff hxs).mp hget
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Set.Finite.card_toFinset hS] using hcard

theorem List.exists_get_eq_of_not_nodup {α : Type} {xs : List α}
    (hxs : ¬ xs.Nodup) :
    ∃ i j : Fin xs.length, i < j ∧ xs.get i = xs.get j := by
  classical
  have hnotinj : ¬ Function.Injective xs.get := by
    intro hinj
    exact hxs (List.nodup_iff_injective_get.mpr hinj)
  simp only [Function.Injective] at hnotinj
  push_neg at hnotinj
  rcases hnotinj with ⟨i, j, hget, hij⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ⟨i, j, hijlt, hget⟩
  · exact ⟨j, i, hjilt, hget.symm⟩

theorem List.exists_get_eq_of_finite_set_card_lt_length {α : Type}
    {xs : List α} (S : Set α) (hS : S.Finite)
    (hmem : ∀ i : Fin xs.length, xs.get i ∈ S)
    (hcard : (Set.Finite.toFinset hS).card < xs.length) :
    ∃ i j : Fin xs.length, i < j ∧ xs.get i = xs.get j := by
  apply List.exists_get_eq_of_not_nodup
  intro hnodup
  have hlen := List.Nodup.length_le_finite_set_card_of_get_mem hnodup S hS hmem
  exact (not_lt_of_ge hlen) hcard

/-- If all intermediates of a shortest `n`-step derivation lie in a finite set `S`, then
there are at most `|S|` step indices. -/
theorem minimal_derivesIn_steps_succ_le_card_of_intermediates_mem
    {g : IndexedGrammar T} {n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂)
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m)
    (S : Set (List g.ISym)) (hS : S.Finite)
    (hmem : ∀ i x, DerivesInIntermediate g n w₁ w₂ i x → x ∈ S) :
    n + 1 ≤ (Set.Finite.toFinset hS).card := by
  classical
  haveI : Fintype S := hS.fintype
  let mid (i : Fin (n + 1)) : List g.ISym :=
    Classical.choose (exists_derivesInIntermediate (g := g)
      (i := i.1) (w₁ := w₁) (w₂ := w₂)
      (Nat.lt_succ_iff.mp i.2) h)
  have hmid (i : Fin (n + 1)) :
      DerivesInIntermediate g n w₁ w₂ i.1 (mid i) :=
    Classical.choose_spec (exists_derivesInIntermediate (g := g)
      (i := i.1) (w₁ := w₁) (w₂ := w₂)
      (Nat.lt_succ_iff.mp i.2) h)
  let f : Fin (n + 1) → S := fun i => ⟨mid i, hmem i.1 (mid i) (hmid i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hsame : mid i = mid j := by
      exact congrArg Subtype.val hij
    exact minimal_derivesIn_intermediate_index_eq (g := g) (n := n) hmin
      (x := mid i) (hmid i) (by simpa [hsame] using hmid j)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Set.Finite.card_toFinset hS] using hcard

theorem generates_iff_exists_derivesIn (g : IndexedGrammar T) (w : List T) :
    g.Generates w ↔
      ∃ n, g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) := by
  rw [Generates, derives_iff_exists_derivesIn]

theorem exists_accepting_derivationTrace_of_generates {g : IndexedGrammar T}
    {w : List T} (hgen : g.Generates w) :
    ∃ n trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) := by
  obtain ⟨n, hder⟩ :=
    (generates_iff_exists_derivesIn g w).mp hgen
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  exact ⟨n, trace, htrace, hlen, hhead, hlast⟩

/-- Any generated word has a propositionally least accepting derivation length. -/
theorem exists_minimal_derivesIn_of_generates {g : IndexedGrammar T}
    {w : List T} (h : g.Generates w) :
    ∃ n, g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      ∀ m, g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m := by
  exact exists_minimal_derivesIn_of_derives (g := g) (by simpa [Generates] using h)

theorem exists_minimal_accepting_derivationTrace_nodup_of_generates {g : IndexedGrammar T}
    {w : List T} (hgen : g.Generates w) :
    ∃ n trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        trace.Nodup := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  exact ⟨n, trace, htrace, hlen, hhead, hlast,
    minimal_derivationTrace_nodup htrace hlen hhead hlast hmin⟩

theorem exists_bound_sententialMaxStackHeight_of_list {g : IndexedGrammar T}
    (trace : List (List g.ISym)) :
    ∃ B : ℕ, ∀ x ∈ trace, sententialMaxStackHeight x ≤ B := by
  induction trace with
  | nil =>
      exact ⟨0, by simp⟩
  | cons x trace ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨max (sententialMaxStackHeight x) B, ?_⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact le_trans (hB y hy) (Nat.le_max_right _ _)

/-- Among all accepting traces with a fixed counted length, choose one with least stack bound.
This is the concrete tie-breaker needed by global stack-control arguments: any other accepting
trace with the same length and stack bound `C` forces the chosen bound to be at most `C`. -/
theorem exists_minimal_stackBound_accepting_derivationTrace_of_derivesIn
    {g : IndexedGrammar T} {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal)) :
    ∃ B : ℕ, ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
        trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        (∀ i (hi : i < trace.length),
          sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
        ∀ C : ℕ,
          (∃ trace' : List (List g.ISym),
            IsDerivationTrace g trace' ∧
              trace'.length = n + 1 ∧
              trace'.head? = some [ISym.indexed g.initial []] ∧
              trace'.getLast? = some (w.map ISym.terminal) ∧
              ∀ i (hi : i < trace'.length),
                sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ C) →
            B ≤ C := by
  let P : ℕ → Prop := fun B =>
    ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
        trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        ∀ i (hi : i < trace.length),
          sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B
  obtain ⟨trace₀, htrace₀, hlen₀, hhead₀, hlast₀⟩ :=
    exists_isDerivationTrace_of_derivesIn h
  obtain ⟨B₀, hB₀⟩ := exists_bound_sententialMaxStackHeight_of_list trace₀
  have hB₀get :
      ∀ i (hi : i < trace₀.length),
        sententialMaxStackHeight (trace₀.get ⟨i, hi⟩) ≤ B₀ := by
    intro i hi
    exact hB₀ (trace₀.get ⟨i, hi⟩) (List.get_mem trace₀ ⟨i, hi⟩)
  obtain ⟨B, hmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (P := P)
      ⟨B₀, trace₀, htrace₀, hlen₀, hhead₀, hlast₀, hB₀get⟩
  rcases hmin.1 with ⟨trace, htrace, hlen, hhead, hlast, hbound⟩
  refine ⟨B, trace, htrace, hlen, hhead, hlast, hbound, ?_⟩
  intro C hC
  rcases le_total C B with hCB | hBC
  · exact hmin.2 hC hCB
  · exact hBC

/-- Generated-word form of the lexicographic choice used by later global arguments: first take
a shortest accepting derivation length, then among traces with that length take one with least
maximum stack bound. -/
theorem exists_shortest_stackBound_minimal_accepting_derivationTrace_of_generates
    {g : IndexedGrammar T} {w : List T} (hgen : g.Generates w) :
    ∃ n : ℕ, ∃ B : ℕ, ∃ trace : List (List g.ISym),
      IsDerivationTrace g trace ∧
        trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
        (∀ m,
          g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
        (∀ i (hi : i < trace.length),
          sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) ∧
        ∀ C : ℕ,
          (∃ trace' : List (List g.ISym),
            IsDerivationTrace g trace' ∧
              trace'.length = n + 1 ∧
              trace'.head? = some [ISym.indexed g.initial []] ∧
              trace'.getLast? = some (w.map ISym.terminal) ∧
              ∀ i (hi : i < trace'.length),
                sententialMaxStackHeight (trace'.get ⟨i, hi⟩) ≤ C) →
            B ≤ C := by
  obtain ⟨n, hder, hminLength⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨B, trace, htrace, hlen, hhead, hlast, hbound, hminBound⟩ :=
    exists_minimal_stackBound_accepting_derivationTrace_of_derivesIn (g := g) hder
  exact ⟨n, B, trace, htrace, hlen, hhead, hlast, hder, hminLength, hbound,
    hminBound⟩

theorem derivesIn_length_le_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂) : w₁.length ≤ w₂.length :=
  derives_length_le_of_noEpsilon hne (derives_of_derivesIn h)

/-! ## Append splitting -/

/-- A one-step indexed rewrite remains valid after appending an unchanged right context. -/
theorem transforms_append_left {g : IndexedGrammar T} {u u' : List g.ISym}
    (h : g.Transforms u u') (v : List g.ISym) :
    g.Transforms (u ++ v) (u' ++ v) := by
  rcases h with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  refine ⟨r, p, q ++ v, σ, hr, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
    | some f =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
  · rw [hw₂]
    simp [List.append_assoc]

/-- A one-step indexed rewrite remains valid after prepending an unchanged left context. -/
theorem transforms_append_right {g : IndexedGrammar T} {v v' : List g.ISym}
    (h : g.Transforms v v') (u : List g.ISym) :
    g.Transforms (u ++ v) (u ++ v') := by
  rcases h with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  refine ⟨r, u ++ p, q, σ, hr, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
    | some f =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
  · rw [hw₂]
    simp [List.append_assoc]

/-- Indexed derivations are closed under appending an unchanged right context. -/
theorem derives_append_left {g : IndexedGrammar T} {u u' : List g.ISym}
    (h : g.Derives u u') (v : List g.ISym) :
    g.Derives (u ++ v) (u' ++ v) := by
  induction h with
  | refl =>
      exact g.deri_self _
  | tail _ hstep ih =>
      exact ih.tail (transforms_append_left hstep v)

/-- Indexed derivations are closed under prepending an unchanged left context. -/
theorem derives_append_right {g : IndexedGrammar T} {v v' : List g.ISym}
    (h : g.Derives v v') (u : List g.ISym) :
    g.Derives (u ++ v) (u ++ v') := by
  induction h with
  | refl =>
      exact g.deri_self _
  | tail _ hstep ih =>
      exact ih.tail (transforms_append_right hstep u)

/-- Independent indexed derivations compose over append. -/
theorem derives_append {g : IndexedGrammar T} {u u' v v' : List g.ISym}
    (hu : g.Derives u u') (hv : g.Derives v v') :
    g.Derives (u ++ v) (u' ++ v') :=
  (derives_append_left hu v).trans (derives_append_right hv u')

/-- Counted indexed derivations are closed under appending an unchanged right context. -/
theorem derivesIn_append_left {g : IndexedGrammar T} {n : ℕ}
    {u u' : List g.ISym}
    (h : g.DerivesIn n u u') (v : List g.ISym) :
    g.DerivesIn n (u ++ v) (u' ++ v) := by
  induction n generalizing u' with
  | zero =>
      have hu : u = u' := by simpa using h
      subst u'
      rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨w ++ v, ih hprev, transforms_append_left hstep v⟩

/-- Counted indexed derivations are closed under prepending an unchanged left context. -/
theorem derivesIn_append_right {g : IndexedGrammar T} {n : ℕ}
    {v v' : List g.ISym}
    (h : g.DerivesIn n v v') (u : List g.ISym) :
    g.DerivesIn n (u ++ v) (u ++ v') := by
  induction n generalizing v' with
  | zero =>
      have hv : v = v' := by simpa using h
      subst v'
      rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨u ++ w, ih hprev, transforms_append_right hstep u⟩

/-- Independent counted indexed derivations compose over append. -/
theorem derivesIn_append {g : IndexedGrammar T} {m n : ℕ}
    {u u' v v' : List g.ISym}
    (hu : g.DerivesIn m u u') (hv : g.DerivesIn n v v') :
    g.DerivesIn (m + n) (u ++ v) (u' ++ v') :=
  derivesIn_trans (derivesIn_append_left hu v) (derivesIn_append_right hv u')

/-- If two sentential forms independently derive terminal words, their append derives the
concatenated terminal word. -/
theorem derives_append_to_terminals_of_derives {g : IndexedGrammar T}
    {u v : List g.ISym} {wu wv : List T}
    (hu : g.Derives u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.Derives v (wv.map fun a => (ISym.terminal a : g.ISym))) :
    g.Derives (u ++ v)
      ((wu ++ wv).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa [List.map_append] using derives_append hu hv

/-- Pair-specialized composition for the binary branch of a normal-form indexed derivation. -/
theorem derives_pair_to_terminals_of_derives {g : IndexedGrammar T}
    {A B : g.nt} {σ τ : List g.flag} {u v : List T}
    (hleft : g.Derives [ISym.indexed A σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed B τ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    g.Derives [ISym.indexed A σ, ISym.indexed B τ]
      ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derives_append_to_terminals_of_derives (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ])
      hleft hright

/-- Counted terminal-word composition over append. -/
theorem derivesIn_append_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {m n : ℕ} {u v : List g.ISym} {wu wv : List T}
    (hu : g.DerivesIn m u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.DerivesIn n v (wv.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (m + n) (u ++ v)
      ((wu ++ wv).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa [List.map_append] using derivesIn_append hu hv

/-- Counted terminal-word composition over three appended sentential regions. -/
theorem derivesIn_append_three_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {nu nv nz : ℕ} {u v z : List g.ISym} {wu wv wz : List T}
    (hu : g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)))
    (hz : g.DerivesIn nz z (wz.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (nu + nv + nz) (u ++ v ++ z)
      ((wu ++ wv ++ wz).map fun a => (ISym.terminal a : g.ISym)) := by
  have huv :=
    derivesIn_append_to_terminals_of_derivesIn (g := g) hu hv
  have huvz :=
    derivesIn_append_to_terminals_of_derivesIn (g := g) huv hz
  simpa [List.map_append, List.append_assoc, Nat.add_assoc] using huvz

/-- Counted terminal-word composition around a distinguished singleton. -/
theorem derivesIn_context_singleton_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {nu ns nv : ℕ} {u v : List g.ISym} {s : g.ISym} {wu ws wv : List T}
    (hu : g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hs : g.DerivesIn ns [s] (ws.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (nu + ns + nv) (u ++ [s] ++ v)
      ((wu ++ ws ++ wv).map fun a => (ISym.terminal a : g.ISym)) :=
  derivesIn_append_three_to_terminals_of_derivesIn (g := g) hu hs hv

/-- Counted terminal-word composition around a distinguished indexed nonterminal. -/
theorem derivesIn_context_indexed_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {nu ns nv : ℕ} {u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    {wu ws wv : List T}
    (hu : g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hs : g.DerivesIn ns [ISym.indexed A σ]
      (ws.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (nu + ns + nv) (u ++ [ISym.indexed A σ] ++ v)
      ((wu ++ ws ++ wv).map fun a => (ISym.terminal a : g.ISym)) :=
  derivesIn_context_singleton_to_terminals_of_derivesIn (g := g) hu hs hv

/-- There is no indexed-grammar rewrite step whose source sentential form is empty. -/
theorem not_transforms_nil {g : IndexedGrammar T} {w : List g.ISym} :
    ¬ g.Transforms ([] : List g.ISym) w := by
  rintro ⟨r, u, v, σ, _hr, hsource, _htarget⟩
  cases hc : r.consume with
  | none =>
      rw [hc] at hsource
      simp at hsource
  | some f =>
      rw [hc] at hsource
      simp at hsource

/-- A counted derivation starting from the empty sentential form is necessarily the
zero-step derivation to the empty sentential form. -/
theorem derivesIn_nil_left_eq {g : IndexedGrammar T} {n : ℕ} {w : List g.ISym}
    (h : g.DerivesIn n ([] : List g.ISym) w) : n = 0 ∧ w = [] := by
  induction n generalizing w with
  | zero =>
      have hw : ([] : List g.ISym) = w := by
        simpa using h
      exact ⟨rfl, hw.symm⟩
  | succ n ih =>
      rcases h with ⟨x, hprev, hstep⟩
      obtain ⟨_hn, hx⟩ := ih hprev
      rw [hx] at hstep
      exact False.elim (not_transforms_nil (g := g) hstep)

/-- Counted terminal-word composition from a positionwise list of singleton derivations. -/
theorem derivesIn_symbols_to_terminals_of_forall₂ {g : IndexedGrammar T}
    {xs : List g.ISym} {parts : List (ℕ × List T)}
    (hparts : List.Forall₂
      (fun s p => g.DerivesIn p.1 [s]
        (p.2.map fun a => (ISym.terminal a : g.ISym)))
      xs parts) :
    g.DerivesIn ((parts.map fun p => p.1).sum) xs
      ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  induction hparts with
  | nil =>
      simp
  | cons hhead _htail ih =>
      have hcomp :=
        derivesIn_append_to_terminals_of_derivesIn (g := g) hhead ih
      simpa [List.map_append] using hcomp

/-- Counted pair-specialized composition for a normal-form binary branch. -/
theorem derivesIn_pair_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {m n : ℕ} {A B : g.nt} {σ τ : List g.flag} {u v : List T}
    (hleft : g.DerivesIn m [ISym.indexed A σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.DerivesIn n [ISym.indexed B τ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (m + n) [ISym.indexed A σ, ISym.indexed B τ]
      ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derivesIn_append_to_terminals_of_derivesIn (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ])
      hleft hright

/-- A one-step indexed rewrite of an appended sentential form rewrites either the left side
or the right side of the append. -/
theorem transforms_append_cases_of_append {g : IndexedGrammar T} {u v w : List g.ISym}
    (hstep : g.Transforms (u ++ v) w) :
    (∃ u', g.Transforms u u' ∧ w = u' ++ v) ∨
      (∃ v', g.Transforms v v' ∧ w = u ++ v') := by
  rcases hstep with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  subst w
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      have hsplit : u ++ v = p ++ ([ISym.indexed r.lhs σ] ++ q) := by
        simpa [List.append_assoc] using hw₁
      rw [List.append_eq_append_iff] at hsplit
      rcases hsplit with ⟨as, hp, hv⟩ | ⟨bs, hu, htail⟩
      · right
        refine ⟨as ++ g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
        · refine ⟨r, as, q, σ, hr, ?_, rfl⟩
          rw [hc]
          simpa [List.append_assoc] using hv
        · rw [hp]
          simp [List.append_assoc]
      · cases bs with
        | nil =>
            right
            refine ⟨g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
            · refine ⟨r, [], q, σ, hr, ?_, rfl⟩
              rw [hc]
              simpa using htail.symm
            · rw [hu]
              simp [List.append_assoc]
        | cons b bs =>
            simp at htail
            rcases htail with ⟨rfl, hq⟩
            left
            refine ⟨p ++ g.expandRhs r.rhs σ ++ bs, ?_, ?_⟩
            · refine ⟨r, p, bs, σ, hr, ?_, rfl⟩
              rw [hc]
              rw [hu]
              simp [List.append_assoc]
            · rw [hq]
              simp [List.append_assoc]
  | some f =>
      rw [hc] at hw₁
      have hsplit : u ++ v = p ++ ([ISym.indexed r.lhs (f :: σ)] ++ q) := by
        simpa [List.append_assoc] using hw₁
      rw [List.append_eq_append_iff] at hsplit
      rcases hsplit with ⟨as, hp, hv⟩ | ⟨bs, hu, htail⟩
      · right
        refine ⟨as ++ g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
        · refine ⟨r, as, q, σ, hr, ?_, rfl⟩
          rw [hc]
          simpa [List.append_assoc] using hv
        · rw [hp]
          simp [List.append_assoc]
      · cases bs with
        | nil =>
            right
            refine ⟨g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
            · refine ⟨r, [], q, σ, hr, ?_, rfl⟩
              rw [hc]
              simpa using htail.symm
            · rw [hu]
              simp [List.append_assoc]
        | cons b bs =>
            simp at htail
            rcases htail with ⟨rfl, hq⟩
            left
            refine ⟨p ++ g.expandRhs r.rhs σ ++ bs, ?_, ?_⟩
            · refine ⟨r, p, bs, σ, hr, ?_, rfl⟩
              rw [hc]
              rw [hu]
              simp [List.append_assoc]
            · rw [hq]
              simp [List.append_assoc]

/-- A counted derivation from an appended sentential form can be factored into counted
derivations from the two sides of the append. The two side budgets add up to the original
budget. -/
theorem derivesIn_append_split {g : IndexedGrammar T} {n : ℕ}
    {u v x : List g.ISym}
    (hder : g.DerivesIn n (u ++ v) x) :
    ∃ m k : ℕ, ∃ u' v' : List g.ISym,
      m + k = n ∧
        x = u' ++ v' ∧
        g.DerivesIn m u u' ∧
        g.DerivesIn k v v' := by
  induction n generalizing x with
  | zero =>
      have hx : u ++ v = x := by simpa using hder
      subst x
      exact ⟨0, 0, u, v, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      rcases hder with ⟨y, hprev, hstep⟩
      rcases ih hprev with ⟨m, k, u', v', hmk, hy, hu, hv⟩
      subst y
      rcases transforms_append_cases_of_append hstep with hleft | hright
      · rcases hleft with ⟨u'', hstepLeft, hx⟩
        refine ⟨m + 1, k, u'', v', ?_, hx, ?_, hv⟩
        · omega
        · exact ⟨u', hu, hstepLeft⟩
      · rcases hright with ⟨v'', hstepRight, hx⟩
        refine ⟨m, k + 1, u', v'', ?_, hx, hu, ?_⟩
        · omega
        · exact ⟨v', hv, hstepRight⟩

theorem append_eq_map_terminal_split {g : IndexedGrammar T}
    {u v : List g.ISym} {w : List T}
    (h : u ++ v = (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ wu wv : List T,
      w = wu ++ wv ∧
        u = (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        v = (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  induction u generalizing w with
  | nil =>
      refine ⟨[], w, by simp, rfl, ?_⟩
      simpa using h
  | cons s u ih =>
      cases w with
      | nil =>
          simp at h
      | cons a w =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          rcases h with ⟨hs, htail⟩
          subst s
          rcases ih htail with ⟨wu, wv, hw, hu, hv⟩
          refine ⟨a :: wu, wv, ?_, ?_, hv⟩
          · simp [hw]
          · simp [hu]

theorem derives_append_to_terminals_split {g : IndexedGrammar T}
    {u v : List g.ISym} {w : List T}
    (hder : g.Derives (u ++ v) (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ wu wv : List T,
      w = wu ++ wv ∧
        g.Derives u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  have haux :
      ∀ {x : List g.ISym},
        g.Derives x (w.map fun a => (ISym.terminal a : g.ISym)) →
        ∀ {u v : List g.ISym}, x = u ++ v →
          ∃ wu wv : List T,
            w = wu ++ wv ∧
              g.Derives u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
    intro x h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro u v hx
        rcases append_eq_map_terminal_split (g := g) hx.symm with ⟨wu, wv, hw, hu, hv⟩
        subst u
        subst v
        exact ⟨wu, wv, hw, g.deri_self _, g.deri_self _⟩
    | @head a c hstep hrest ih =>
        intro u v hx
        subst a
        rcases transforms_append_cases_of_append hstep with hleft | hright
        · rcases hleft with ⟨u', hu', hc⟩
          rcases ih hc with ⟨wu, wv, hw, huder, hvder⟩
          exact ⟨wu, wv, hw, (deri_of_tran hu').trans huder, hvder⟩
        · rcases hright with ⟨v', hv', hc⟩
          rcases ih hc with ⟨wu, wv, hw, huder, hvder⟩
          exact ⟨wu, wv, hw, huder, (deri_of_tran hv').trans hvder⟩
  exact haux hder rfl

theorem derives_pair_to_terminals_split {g : IndexedGrammar T}
    {A B : g.nt} {σ τ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ, ISym.indexed B τ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ u v : List T,
      w = u ++ v ∧
        g.Derives [ISym.indexed A σ] (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed B τ] (v.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derives_append_to_terminals_split (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ]) (w := w) hder

/-- Counted split of an appended terminal derivation. -/
theorem derivesIn_append_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} {w : List T}
    (hder : g.DerivesIn n (u ++ v)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ wu wv : List T,
      m + k = n ∧
        w = wu ++ wv ∧
        g.DerivesIn m u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases derivesIn_append_split (g := g) hder with ⟨m, k, u', v', hmk, hx, hu, hv⟩
  rcases append_eq_map_terminal_split (g := g) hx.symm with
    ⟨wu, wv, hw, hu', hv'⟩
  subst u'
  subst v'
  exact ⟨m, k, wu, wv, hmk, hw, hu, hv⟩

/-- Counted split of a terminal derivation from three appended regions. The budgets for the
three independent regions add up to the original budget. -/
theorem derivesIn_append_three_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {u v z : List g.ISym} {w : List T}
    (hder : g.DerivesIn n (u ++ v ++ z)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ nu nv nz : ℕ, ∃ wu wv wz : List T,
      nu + nv + nz = n ∧
        w = wu ++ wv ++ wz ∧
        g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nz z (wz.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases derivesIn_append_to_terminals_split
      (g := g) (u := u ++ v) (v := z) hder with
    ⟨nuv, nz, wuv, wz, hnuvz, hwuvz, huv, hz⟩
  rcases derivesIn_append_to_terminals_split
      (g := g) (u := u) (v := v) huv with
    ⟨nu, nv, wu, wv, hnuv, hwuv, hu, hv⟩
  refine ⟨nu, nv, nz, wu, wv, wz, ?_, ?_, hu, hv, hz⟩
  · omega
  · rw [hwuvz, hwuv]

/-- Counted split around a distinguished singleton in the middle of a sentential form. -/
theorem derivesIn_context_singleton_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} {s : g.ISym} {w : List T}
    (hder : g.DerivesIn n (u ++ [s] ++ v)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ nu ns nv : ℕ, ∃ wu ws wv : List T,
      nu + ns + nv = n ∧
        w = wu ++ ws ++ wv ∧
        ws.Sublist w ∧
        g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn ns [s] (ws.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases derivesIn_append_three_to_terminals_split
      (g := g) (u := u) (v := [s]) (z := v) hder with
    ⟨nu, ns, nv, wu, ws, wv, hsum, hw, hu, hs, hv⟩
  have hws : ws.Sublist w := by
    subst w
    exact (List.sublist_append_right wu ws).trans
      (List.sublist_append_left (wu ++ ws) wv)
  exact ⟨nu, ns, nv, wu, ws, wv, hsum, hw, hws, hu, hs, hv⟩

/-- Counted split around a distinguished indexed nonterminal in the middle of a sentential
form. This exposes the terminal subword and local counted derivation generated by that one
indexed symbol. -/
theorem derivesIn_context_indexed_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn n (u ++ [ISym.indexed A σ] ++ v)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ nu ns nv : ℕ, ∃ wu ws wv : List T,
      nu + ns + nv = n ∧
        w = wu ++ ws ++ wv ∧
        ws.Sublist w ∧
        g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn ns [ISym.indexed A σ]
          (ws.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derivesIn_context_singleton_to_terminals_split
      (g := g) (u := u) (v := v) (s := ISym.indexed A σ) hder

/-- Counted split of a terminal derivation from an arbitrary sentential form into
positionwise singleton derivations. The list `parts` records, for each source symbol, the
number of rewrite steps and the terminal subword it contributes. -/
theorem derivesIn_symbols_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {xs : List g.ISym} {w : List T}
    (hder : g.DerivesIn n xs (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ parts : List (ℕ × List T),
      parts.length = xs.length ∧
        (parts.map fun p => p.1).sum = n ∧
        (parts.flatMap fun p => p.2) = w ∧
        List.Forall₂
          (fun s p => g.DerivesIn p.1 [s]
            (p.2.map fun a => (ISym.terminal a : g.ISym)))
          xs parts := by
  induction xs generalizing n w with
  | nil =>
      obtain ⟨hn, htarget⟩ := derivesIn_nil_left_eq (g := g) hder
      have hw : w = [] := by
        simpa using htarget
      subst n
      subst w
      exact ⟨[], by simp, by simp, by simp, List.Forall₂.nil⟩
  | cons s xs ih =>
      have hder' : g.DerivesIn n ([s] ++ xs)
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
        simpa using hder
      rcases derivesIn_append_to_terminals_split
          (g := g) (u := [s]) (v := xs) (w := w) hder' with
        ⟨m, k, wu, wv, hmk, hw, hhead, htail⟩
      rcases ih htail with ⟨parts, hlen, hsum, hflat, hparts⟩
      refine ⟨(m, wu) :: parts, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp [hsum, hmk]
      · simp [hw, hflat]
      · exact List.Forall₂.cons hhead hparts

/-- At any position of an accepting trace, the remaining suffix derivation splits across the
whole sentential form at that position. Each entry of `parts` gives the exact remaining
rewrite budget and terminal subword for the corresponding source symbol. -/
theorem accepting_derivationTrace_symbols_suffix_to_terminals_split
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hi : i < trace.length) :
    ∃ parts : List (ℕ × List T),
      parts.length = (trace.get ⟨i, hi⟩).length ∧
        (parts.map fun p => p.1).sum = trace.length - 1 - i ∧
        (parts.flatMap fun p => p.2) = w ∧
        List.Forall₂
          (fun s p => g.DerivesIn p.1 [s]
            (p.2.map fun a => (ISym.terminal a : g.ISym)))
          (trace.get ⟨i, hi⟩) parts := by
  have hsuffix :=
    isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
  exact derivesIn_symbols_to_terminals_split (g := g) hsuffix

/-- If an indexed symbol occurs with explicit left and right context at an accepting trace
position, the suffix of the trace exposes the terminal subword generated by that one symbol. -/
theorem accepting_derivationTrace_indexed_context_suffix_to_terminals_split
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A σ] ++ v) :
    ∃ nu ns nv : ℕ, ∃ wu ws wv : List T,
      nu + ns + nv = trace.length - 1 - i ∧
        w = wu ++ ws ++ wv ∧
        ws.Sublist w ∧
        g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn ns [ISym.indexed A σ]
          (ws.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  have hsuffix :=
    isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
  rw [hctx] at hsuffix
  exact derivesIn_context_indexed_to_terminals_split (g := g) hsuffix

/-- Length-bounded projection of
`accepting_derivationTrace_indexed_context_suffix_to_terminals_split`, retaining only the
local counted derivation generated by the distinguished indexed symbol. -/
theorem accepting_derivationTrace_indexed_context_exists_local_derivesIn
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {L i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {σ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A σ] ++ v) :
    ∃ ns : ℕ, ∃ ws : List T,
      ws.Sublist w ∧ ws.length ≤ L ∧
        g.DerivesIn ns [ISym.indexed A σ]
          (ws.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases accepting_derivationTrace_indexed_context_suffix_to_terminals_split
      (g := g) htrace hlast hi hctx with
    ⟨_nu, ns, _nv, _wu, ws, _wv, _hsum, _hw, hws, _hu, hs, _hv⟩
  exact ⟨ns, ws, hws, le_trans hws.length_le hwlen, hs⟩

/-- Replace the local terminal derivation of a distinguished indexed symbol inside an
accepting-trace suffix. This keeps the left and right context derivations from the original
suffix split and swaps only the local derivation of the indexed symbol. -/
theorem accepting_derivationTrace_indexed_context_suffix_replacement
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hi : i < trace.length)
    {u v : List g.ISym} {A : g.nt} {σ τ : List g.flag}
    (hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A σ] ++ v)
    (hreplace :
      ∀ n : ℕ, ∀ localWord : List T,
        g.DerivesIn n [ISym.indexed A σ]
          (localWord.map fun a => (ISym.terminal a : g.ISym)) →
        ∃ m : ℕ,
          g.DerivesIn m [ISym.indexed A τ]
            (localWord.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ n : ℕ,
      g.DerivesIn n (u ++ [ISym.indexed A τ] ++ v)
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases accepting_derivationTrace_indexed_context_suffix_to_terminals_split
      (g := g) htrace hlast hi hctx with
    ⟨nu, ns, nv, wu, ws, wv, _hsum, hw, _hws, hu, hs, hv⟩
  obtain ⟨m, hτ⟩ := hreplace ns ws hs
  refine ⟨nu + m + nv, ?_⟩
  have hnew :=
    derivesIn_context_indexed_to_terminals_of_derivesIn
      (g := g) (u := u) (v := v) (A := A) (σ := τ)
      (nu := nu) (ns := m) (nv := nv)
      (wu := wu) (ws := ws) (wv := wv) hu hτ hv
  simpa [hw] using hnew

/-- Membership-facing version of
`accepting_derivationTrace_indexed_context_suffix_to_terminals_split`. -/
theorem accepting_derivationTrace_indexed_mem_suffix_to_terminals_split
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hi : i < trace.length)
    {A : g.nt} {σ : List g.flag}
    (hmem : ISym.indexed A σ ∈ trace.get ⟨i, hi⟩) :
    ∃ u v : List g.ISym, ∃ nu ns nv : ℕ, ∃ wu ws wv : List T,
      trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A σ] ++ v ∧
        nu + ns + nv = trace.length - 1 - i ∧
        w = wu ++ ws ++ wv ∧
        ws.Sublist w ∧
        g.DerivesIn nu u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn ns [ISym.indexed A σ]
          (ws.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn nv v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases (List.mem_iff_append.mp hmem) with ⟨u, v, hctx0⟩
  have hctx : trace.get ⟨i, hi⟩ = u ++ [ISym.indexed A σ] ++ v := by
    simpa using hctx0
  rcases accepting_derivationTrace_indexed_context_suffix_to_terminals_split
      (g := g) htrace hlast hi hctx with
    ⟨nu, ns, nv, wu, ws, wv, hsum, hw, hws, hu, hs, hv⟩
  exact ⟨u, v, nu, ns, nv, wu, ws, wv, hctx, hsum, hw, hws, hu, hs, hv⟩

/-- Length-bounded membership-facing local derivation generated by an indexed symbol in an
accepting trace. -/
theorem accepting_derivationTrace_indexed_mem_exists_local_derivesIn
    {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w : List T} {L i : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hi : i < trace.length)
    {A : g.nt} {σ : List g.flag}
    (hmem : ISym.indexed A σ ∈ trace.get ⟨i, hi⟩) :
    ∃ ns : ℕ, ∃ ws : List T,
      ws.Sublist w ∧ ws.length ≤ L ∧
        g.DerivesIn ns [ISym.indexed A σ]
          (ws.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases accepting_derivationTrace_indexed_mem_suffix_to_terminals_split
      (g := g) htrace hlast hi hmem with
    ⟨_u, _v, _nu, ns, _nv, _wu, ws, _wv, _hctx, _hsum, _hw, hws, _hu, hs, _hv⟩
  exact ⟨ns, ws, hws, le_trans hws.length_le hwlen, hs⟩

/-- Counted split for the pair produced by a normal-form binary branch. -/
theorem derivesIn_pair_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {A B : g.nt} {σ τ : List g.flag} {w : List T}
    (hder : g.DerivesIn n [ISym.indexed A σ, ISym.indexed B τ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        g.DerivesIn m [ISym.indexed A σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k [ISym.indexed B τ]
          (v.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derivesIn_append_to_terminals_split (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ]) (w := w) hder

theorem not_transforms_from_terminals {g : IndexedGrammar T}
    {w : List T} {x : List g.ISym} :
    ¬ g.Transforms (w.map fun a => (ISym.terminal a : g.ISym)) x := by
  intro h
  rcases h with ⟨r, u, v, σ, _hr, hw₁, _hw₂⟩
  have hcount :
      sententialNonterminalCount (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
    simp [sententialNonterminalCount]
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      rw [hw₁] at hcount
      simp [List.append_assoc] at hcount
  | some f =>
      rw [hc] at hw₁
      rw [hw₁] at hcount
      simp [List.append_assoc] at hcount

theorem derives_from_terminals_eq {g : IndexedGrammar T}
    {u : List T} {w : List g.ISym}
    (hder : g.Derives (u.map fun a => (ISym.terminal a : g.ISym)) w) :
    w = u.map fun a => (ISym.terminal a : g.ISym) := by
  induction hder with
  | refl =>
      rfl
  | tail _ hstep ih =>
      rw [ih] at hstep
      exact False.elim (not_transforms_from_terminals hstep)

theorem derives_terminals_inj {g : IndexedGrammar T}
    {u w : List T}
    (hder : g.Derives (u.map fun a => (ISym.terminal a : g.ISym))
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    w = u := by
  have h := derives_from_terminals_eq (g := g) hder
  have hmap : w.map (fun a => (ISym.terminal a : g.ISym)) =
      u.map fun a => (ISym.terminal a : g.ISym) := h
  exact (Function.Injective.list_map (fun a b hab => by simpa using hab)) hmap

theorem derives_terminal_singleton_eq {g : IndexedGrammar T}
    {a : T} {w : List T}
    (hder : g.Derives [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    w = [a] := by
  simpa using
    derives_terminals_inj (g := g) (u := [a]) (w := w) hder

theorem derivesIn_from_terminals_eq {g : IndexedGrammar T}
    {n : ℕ} {u : List T} {w : List g.ISym}
    (hder : g.DerivesIn n
      (u.map fun a => (ISym.terminal a : g.ISym)) w) :
    w = u.map fun a => (ISym.terminal a : g.ISym) :=
  derives_from_terminals_eq (g := g) (derives_of_derivesIn hder)

theorem not_derivesIn_succ_from_terminals {g : IndexedGrammar T}
    {n : ℕ} {u : List T} {w : List g.ISym} :
    ¬ g.DerivesIn (n + 1)
      (u.map fun a => (ISym.terminal a : g.ISym)) w := by
  intro hder
  rcases hder with ⟨x, hprev, hstep⟩
  have hx := derivesIn_from_terminals_eq (g := g) hprev
  subst x
  exact not_transforms_from_terminals hstep

theorem derivesIn_terminal_singleton_eq {g : IndexedGrammar T}
    {n : ℕ} {a : T} {w : List T}
    (hder : g.DerivesIn n [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    w = [a] := by
  exact derives_terminal_singleton_eq (g := g) (derives_of_derivesIn hder)

theorem derivesIn_terminal_singleton_steps_eq_zero {g : IndexedGrammar T}
    {n : ℕ} {a : T} {w : List T}
    (hder : g.DerivesIn n [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      exact False.elim
        (not_derivesIn_succ_from_terminals (g := g) (n := n) (u := [a]) hder)

/-! ## Terminal-yield monotonicity -/

/-- A single indexed-grammar rewrite never deletes or reorders terminals already present in the
sentential form. -/
theorem transforms_sententialTerminals_sublist {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (sententialTerminals w₁).Sublist (sententialTerminals w₂) := by
  rcases h with ⟨r, u, v, σ, _hr, hw₁, hw₂⟩
  cases hconsume : r.consume with
  | none =>
      rw [hconsume] at hw₁
      rw [hw₁, hw₂]
      simp only [sententialTerminals_append, sententialTerminals_indexed, List.append_nil]
      exact
        List.Sublist.append
          (List.sublist_append_left (sententialTerminals u)
            (sententialTerminals (g.expandRhs r.rhs σ)))
          (List.Sublist.refl (sententialTerminals v))
  | some f =>
      rw [hconsume] at hw₁
      rw [hw₁, hw₂]
      simp only [sententialTerminals_append, sententialTerminals_indexed, List.append_nil]
      exact
        List.Sublist.append
          (List.sublist_append_left (sententialTerminals u)
            (sententialTerminals (g.expandRhs r.rhs σ)))
          (List.Sublist.refl (sententialTerminals v))

theorem transforms_terminalCount_le {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₁ ≤ sententialTerminalCount w₂ := by
  have hsub := transforms_sententialTerminals_sublist (g := g) h
  simpa using hsub.length_le

theorem derivesIn_sententialTerminals_sublist {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    (sententialTerminals w₁).Sublist (sententialTerminals w₂) := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact List.Sublist.refl _
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact (ih hprev).trans (transforms_sententialTerminals_sublist hstep)

theorem derivesIn_terminalCount_le {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    sententialTerminalCount w₁ ≤ sententialTerminalCount w₂ := by
  have hsub := derivesIn_sententialTerminals_sublist (g := g) h
  simpa using hsub.length_le

theorem derives_sententialTerminals_sublist {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    (sententialTerminals w₁).Sublist (sententialTerminals w₂) := by
  induction h with
  | refl =>
      exact List.Sublist.refl _
  | tail _ hstep ih =>
      exact ih.trans (transforms_sententialTerminals_sublist hstep)

theorem derives_terminalCount_le {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    sententialTerminalCount w₁ ≤ sententialTerminalCount w₂ := by
  have hsub := derives_sententialTerminals_sublist (g := g) h
  simpa using hsub.length_le

private theorem max_push_le_succ (a b c : ℕ) :
    max a (max (b + 1) c) ≤ max a (max b c) + 1 := by
  apply Nat.max_le.mpr
  constructor
  · exact le_trans (Nat.le_max_left a (max b c)) (Nat.le_succ _)
  · apply Nat.max_le.mpr
    constructor
    · have hb : b ≤ max a (max b c) :=
        le_trans (Nat.le_max_left b c) (Nat.le_max_right a (max b c))
      exact Nat.succ_le_succ hb
    · have hc : c ≤ max a (max b c) :=
        le_trans (Nat.le_max_right b c) (Nat.le_max_right a (max b c))
      exact le_trans hc (Nat.le_succ _)

private theorem max_pop_le (a b c : ℕ) :
    max a (max b c) ≤ max a (max (b + 1) c) := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_max_left a (max (b + 1) c)
  · apply Nat.max_le.mpr
    constructor
    · exact le_trans (le_trans (Nat.le_succ b) (Nat.le_max_left (b + 1) c))
        (Nat.le_max_right a (max (b + 1) c))
    · exact le_trans (Nat.le_max_right (b + 1) c)
        (Nat.le_max_right a (max (b + 1) c))

private theorem max_pop_le_succ (a b c : ℕ) :
    max a (max b c) ≤ max a (max (b + 1) c) + 1 := by
  exact le_trans (max_pop_le a b c) (Nat.le_succ _)

private theorem max_drop_middle_le (a b c : ℕ) :
    max a c ≤ max a (max b c) := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_max_left a (max b c)
  · exact le_trans (Nat.le_max_right b c) (Nat.le_max_right a (max b c))

private theorem max_terminal_le_succ (a b c : ℕ) :
    max a c ≤ max a (max b c) + 1 := by
  exact le_trans (max_drop_middle_le a b c) (Nat.le_succ _)

theorem sententialMaxStackHeight_context_binary_eq {g : IndexedGrammar T}
    {u v : List g.ISym} {A B C : g.nt} {σ : List g.flag} :
    sententialMaxStackHeight (u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v) =
      sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) := by
  simp [List.append_assoc, Nat.max_comm]

theorem sententialMaxStackHeight_context_pop_le {g : IndexedGrammar T}
    {u v : List g.ISym} {A B : g.nt} {f : g.flag} {ρ : List g.flag} :
    sententialMaxStackHeight (u ++ [ISym.indexed B ρ] ++ v) ≤
      sententialMaxStackHeight (u ++ [ISym.indexed A (f :: ρ)] ++ v) := by
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_pop_le (sententialMaxStackHeight u) ρ.length (sententialMaxStackHeight v)

theorem sententialMaxStackHeight_context_push_le_succ {g : IndexedGrammar T}
    {u v : List g.ISym} {A B : g.nt} {f : g.flag} {σ : List g.flag} :
    sententialMaxStackHeight (u ++ [ISym.indexed B (f :: σ)] ++ v) ≤
      sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) + 1 := by
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_push_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

theorem sententialMaxStackHeight_context_terminal_le {g : IndexedGrammar T}
    {u v : List g.ISym} {A : g.nt} {a : T} {σ : List g.flag} :
    sententialMaxStackHeight (u ++ [ISym.terminal a] ++ v) ≤
      sententialMaxStackHeight (u ++ [ISym.indexed A σ] ++ v) := by
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_drop_middle_le (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

/-! ## Normal-form step bounds -/

theorem IRule.rhs_length_eq_one_or_two_of_isNF {N F : Type} [DecidableEq N]
    {r : IRule T N F} {start : N} (hNF : IRule.IsNF r start) :
    r.rhs.length = 1 ∨ r.rhs.length = 2 := by
  rcases hNF with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨_, _, _, hrhs, _, _⟩
    right
    simp [hrhs]
  · rcases hpop with ⟨_, _, _, hrhs, _⟩
    left
    simp [hrhs]
  · rcases hpush with ⟨_, _, _, hrhs, _⟩
    left
    simp [hrhs]
  · rcases hterm with ⟨_, _, hrhs⟩
    left
    simp [hrhs]

theorem IRule.rhs_length_le_two_of_isNF {N F : Type} [DecidableEq N]
    {r : IRule T N F} {start : N} (hNF : IRule.IsNF r start) :
    r.rhs.length ≤ 2 := by
  rcases IRule.rhs_length_eq_one_or_two_of_isNF (T := T) hNF with h | h <;> omega

theorem expandRhs_length (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (g.expandRhs rhs σ).length = rhs.length := by
  simp [expandRhs]

/-- A normal-form step either preserves sentential-form length or increases it by one. -/
theorem transforms_length_eq_or_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    w₂.length = w₁.length ∨ w₂.length = w₁.length + 1 := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  subst w₂
  rcases hNF r hr with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, _, _⟩
    rw [hc] at hw₁
    subst w₁
    right
    simp [expandRhs, hrhs, List.length_append]
    omega
  · rcases hpop with ⟨f, hc, B, hrhs, _⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]
  · rcases hpush with ⟨hc, B, f, hrhs, _⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]
  · rcases hterm with ⟨hc, a, hrhs⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]

theorem transforms_length_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    w₂.length ≤ w₁.length + 1 := by
  rcases transforms_length_eq_or_succ_of_isNormalForm hNF h with hlen | hlen <;> omega

/-- A normal-form binary split step `A[σ] ↦ B[σ] C[σ]`. -/
def TransformIsBinaryStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧ C ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v

/-- A normal-form flag-pop step `A[f :: σ] ↦ B[σ]`. -/
def TransformIsPopStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A (f :: σ)] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ] ++ v

/-- A normal-form flag-push step `A[σ] ↦ B[f :: σ]`. -/
def TransformIsPushStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B (f :: σ)] ++ v

/-- A normal-form terminal-emission step `A[σ] ↦ a`. -/
def TransformIsTerminalStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.terminal a] ++ v

/-- A one-step rewrite in normal form has exactly one of the four indexed-normal-form
shapes: binary split, flag pop, flag push, or terminal emission. -/
theorem transforms_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧ C ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A (f :: σ)] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B (f :: σ)] ++ v) ∨
    (∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.terminal a] ++ v) := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  rcases hNF r hr with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
    left
    refine ⟨r.lhs, B, C, u, v, σ, hB, hC, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
    right
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hterm with ⟨hc, a, hrhs⟩
    right
    right
    right
    refine ⟨r.lhs, a, u, v, σ, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]

theorem transforms_kind_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsBinaryStep g w₁ w₂ ∨
      TransformIsPopStep g w₁ w₂ ∨
      TransformIsPushStep g w₁ w₂ ∨
      TransformIsTerminalStep g w₁ w₂ := by
  simpa [TransformIsBinaryStep, TransformIsPopStep, TransformIsPushStep,
    TransformIsTerminalStep] using transforms_cases_of_isNormalForm hNF h

theorem flatTransforms_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {x y : List (FlatSymbol T g.nt g.flag)} (h : FlatTransforms g x y) :
    (∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧ C ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B σ) ++
        encodeISym (ISym.indexed C σ) ++ encodeSentential v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A (f :: σ)) ++
        encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B σ) ++ encodeSentential v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B (f :: σ)) ++
        encodeSentential v) ∨
    (∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.terminal a) ++ encodeSentential v) := by
  rcases (flatTransforms_iff_exists_encoded_transform.mp h) with
    ⟨w₁, w₂, hx, hy, hstep⟩
  rcases transforms_kind_cases_of_isNormalForm hNF hstep with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, hB, hC, hw₁, hw₂⟩
    subst w₁
    subst w₂
    left
    refine ⟨A, B, C, u, v, σ, hB, hC, ?_, ?_⟩
    · rw [hx]
      simp [encodeSentential_append, List.append_assoc]
    · rw [hy]
      simp [encodeSentential_append, List.append_assoc]
  · rcases hpop with ⟨A, B, f, u, v, σ, hB, hw₁, hw₂⟩
    subst w₁
    subst w₂
    right
    left
    refine ⟨A, B, f, u, v, σ, hB, ?_, ?_⟩
    · rw [hx]
      simp [encodeSentential_append, List.append_assoc]
    · rw [hy]
      simp [encodeSentential_append, List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, hB, hw₁, hw₂⟩
    subst w₁
    subst w₂
    right
    right
    left
    refine ⟨A, B, f, u, v, σ, hB, ?_, ?_⟩
    · rw [hx]
      simp [encodeSentential_append, List.append_assoc]
    · rw [hy]
      simp [encodeSentential_append, List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    subst w₁
    subst w₂
    right
    right
    right
    refine ⟨A, a, u, v, σ, ?_, ?_⟩
    · rw [hx]
      simp [encodeSentential_append, List.append_assoc]
    · rw [hy]
      simp [encodeSentential_append, List.append_assoc]

theorem flatTransforms_rule_cases_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {x y : List (FlatSymbol T g.nt g.flag)} :
    FlatTransforms g x y ↔
    (∃ r ∈ g.rules, ∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      r.lhs = A ∧ r.consume = none ∧
      r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
      B ≠ g.initial ∧ C ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B σ) ++
        encodeISym (ISym.indexed C σ) ++ encodeSentential v) ∨
    (∃ r ∈ g.rules, ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym,
      ∃ σ : List g.flag,
      r.lhs = A ∧ r.consume = some f ∧
      r.rhs = [IRhsSymbol.nonterminal B none] ∧ B ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A (f :: σ)) ++
        encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B σ) ++ encodeSentential v) ∨
    (∃ r ∈ g.rules, ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym,
      ∃ σ : List g.flag,
      r.lhs = A ∧ r.consume = none ∧
      r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧ B ≠ g.initial ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.indexed B (f :: σ)) ++
        encodeSentential v) ∨
    (∃ r ∈ g.rules, ∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
      x = encodeSentential u ++ encodeISym (ISym.indexed A σ) ++ encodeSentential v ∧
      y = encodeSentential u ++ encodeISym (ISym.terminal a) ++ encodeSentential v) := by
  constructor
  · intro hflat
    rcases (flatTransforms_iff_exists_encoded_transform.mp hflat) with
      ⟨w₁, w₂, hx, hy, r, u, v, σ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
      rw [hc] at hw₁
      left
      refine ⟨r, hr, r.lhs, B, C, u, v, σ, rfl, hc, hrhs, hB, hC, ?_, ?_⟩
      · rw [hx, hw₁]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy, hw₂, hrhs]
        simp [expandRhs, encodeSentential_append, List.append_assoc]
    · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
      rw [hc] at hw₁
      right
      left
      refine ⟨r, hr, r.lhs, B, f, u, v, σ, rfl, hc, hrhs, hB, ?_, ?_⟩
      · rw [hx, hw₁]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy, hw₂, hrhs]
        simp [expandRhs, encodeSentential_append, List.append_assoc]
    · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
      rw [hc] at hw₁
      right
      right
      left
      refine ⟨r, hr, r.lhs, B, f, u, v, σ, rfl, hc, hrhs, hB, ?_, ?_⟩
      · rw [hx, hw₁]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy, hw₂, hrhs]
        simp [expandRhs, encodeSentential_append, List.append_assoc]
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      right
      right
      right
      refine ⟨r, hr, r.lhs, a, u, v, σ, rfl, hc, hrhs, ?_, ?_⟩
      · rw [hx, hw₁]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy, hw₂, hrhs]
        simp [expandRhs, encodeSentential_append, List.append_assoc]
  · intro hcases
    apply flatTransforms_iff_exists_encoded_transform.mpr
    rcases hcases with hbin | hpop | hpush | hterm
    · rcases hbin with
        ⟨r, hr, A, B, C, u, v, σ, hlhs, hc, hrhs, _hB, _hC, hx, hy⟩
      refine ⟨u ++ [ISym.indexed A σ] ++ v,
        u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v, ?_, ?_, ?_⟩
      · rw [hx]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy]
        simp [encodeSentential_append, List.append_assoc]
      · refine ⟨r, u, v, σ, hr, ?_, ?_⟩
        · rw [hc, hlhs]
        · rw [hrhs]
          simp [expandRhs]
    · rcases hpop with
        ⟨r, hr, A, B, f, u, v, σ, hlhs, hc, hrhs, _hB, hx, hy⟩
      refine ⟨u ++ [ISym.indexed A (f :: σ)] ++ v,
        u ++ [ISym.indexed B σ] ++ v, ?_, ?_, ?_⟩
      · rw [hx]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy]
        simp [encodeSentential_append, List.append_assoc]
      · refine ⟨r, u, v, σ, hr, ?_, ?_⟩
        · rw [hc, hlhs]
        · rw [hrhs]
          simp [expandRhs]
    · rcases hpush with
        ⟨r, hr, A, B, f, u, v, σ, hlhs, hc, hrhs, _hB, hx, hy⟩
      refine ⟨u ++ [ISym.indexed A σ] ++ v,
        u ++ [ISym.indexed B (f :: σ)] ++ v, ?_, ?_, ?_⟩
      · rw [hx]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy]
        simp [encodeSentential_append, List.append_assoc]
      · refine ⟨r, u, v, σ, hr, ?_, ?_⟩
        · rw [hc, hlhs]
        · rw [hrhs]
          simp [expandRhs]
    · rcases hterm with
        ⟨r, hr, A, a, u, v, σ, hlhs, hc, hrhs, hx, hy⟩
      refine ⟨u ++ [ISym.indexed A σ] ++ v,
        u ++ [ISym.terminal a] ++ v, ?_, ?_, ?_⟩
      · rw [hx]
        simp [encodeSentential_append, List.append_assoc]
      · rw [hy]
        simp [encodeSentential_append, List.append_assoc]
      · refine ⟨r, u, v, σ, hr, ?_, ?_⟩
        · rw [hc, hlhs]
        · rw [hrhs]
          simp [expandRhs]

theorem transformIsBinaryStep_encodeSentential_length_eq
    {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : TransformIsBinaryStep g w₁ w₂) :
    ∃ σ : List g.flag,
      σ.length ≤ sententialMaxStackHeight w₁ ∧
      (encodeSentential w₂).length =
        (encodeSentential w₁).length + σ.length + 2 := by
  rcases h with ⟨A, B, C, u, v, σ, _hB, _hC, hw₁, hw₂⟩
  subst w₁
  subst w₂
  refine ⟨σ, ?_, ?_⟩
  · have hσ :
        σ.length ≤ max (max (sententialMaxStackHeight u) σ.length)
          (sententialMaxStackHeight v) :=
      le_trans (Nat.le_max_right (sententialMaxStackHeight u) σ.length)
        (Nat.le_max_left (max (sententialMaxStackHeight u) σ.length)
          (sententialMaxStackHeight v))
    simpa only [sententialMaxStackHeight_append, sententialMaxStackHeight_indexed] using hσ
  · simp [List.length_append]
    omega

theorem transformIsPopStep_encodeSentential_length_le
    {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : TransformIsPopStep g w₁ w₂) :
    (encodeSentential w₂).length ≤ (encodeSentential w₁).length := by
  rcases h with ⟨A, B, f, u, v, σ, _hB, hw₁, hw₂⟩
  subst w₁
  subst w₂
  simp [List.length_append]

theorem transformIsPushStep_encodeSentential_length_eq
    {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : TransformIsPushStep g w₁ w₂) :
    (encodeSentential w₂).length = (encodeSentential w₁).length + 1 := by
  rcases h with ⟨A, B, f, u, v, σ, _hB, hw₁, hw₂⟩
  subst w₁
  subst w₂
  simp [List.length_append]
  omega

theorem transformIsTerminalStep_encodeSentential_length_le
    {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (h : TransformIsTerminalStep g w₁ w₂) :
    (encodeSentential w₂).length ≤ (encodeSentential w₁).length := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  subst w₁
  subst w₂
  simp [List.length_append]
  omega

theorem transforms_encodeSentential_length_le_add_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂)
    (hmax : sententialMaxStackHeight w₁ ≤ B) :
    (encodeSentential w₂).length ≤ (encodeSentential w₁).length + B + 2 := by
  rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · obtain ⟨σ, hσ, hlen⟩ := transformIsBinaryStep_encodeSentential_length_eq hbin
    rw [hlen]
    omega
  · have hlen := transformIsPopStep_encodeSentential_length_le hpop
    omega
  · have hlen := transformIsPushStep_encodeSentential_length_eq hpush
    rw [hlen]
    omega
  · have hlen := transformIsTerminalStep_encodeSentential_length_le hterm
    omega

/-- A singleton indexed symbol can only match a one-rule redex with empty context. -/
private theorem singleton_indexed_eq_context_bounds {g : IndexedGrammar T}
    {A B : g.nt} {σ τ : List g.flag} {u v : List g.ISym}
    (h : [ISym.indexed A σ] = u ++ [ISym.indexed B τ] ++ v) :
    u = [] ∧ v = [] ∧ A = B ∧ σ = τ := by
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons x xs =>
        have hlen := congrArg List.length h
        simp at hlen
  subst u
  have h' : [ISym.indexed A σ] = ISym.indexed B τ :: v := by
    simpa using h
  simp at h'
  rcases h' with ⟨⟨hA, hσ⟩, hv⟩
  exact ⟨rfl, hv, hA, hσ⟩

theorem transforms_singleton_binary_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B C : g.nt} {σ : List g.flag} :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨hB, hC⟩
      subst B₀
      subst C₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hpop with ⟨f, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpush with ⟨hc, B₀, f, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_pop_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B : g.nt} {f : g.flag} {ρ : List g.flag} :
    g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f₀, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hstack⟩
      subst u
      subst v
      simp at hstack
      rcases hstack with ⟨hf, hτ⟩
      subst f₀
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      subst B₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hpush with ⟨hc, B₀, f₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨_, hout⟩
      subst τ
      have hlen := congrArg List.length hout
      simp at hlen
      omega
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], ρ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_push_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B : g.nt} {f : g.flag} {σ : List g.flag} :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f₀, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨_, hout⟩
      subst σ
      have hlen := congrArg List.length hout
      simp at hlen
      omega
    · rcases hpush with ⟨hc, B₀, f₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨hB, hf⟩
      subst B₀
      subst f₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_terminal_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {a : T} :
    g.Transforms [ISym.indexed A σ] [ISym.terminal a] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpush with ⟨hc, B₀, f, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hterm with ⟨hc, a₀, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      subst a₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

/-- First-step analysis for a terminal derivation from one indexed nonterminal in normal form.
The first rule is exposed, and the rest of the terminal derivation is split along the symbols
created by that first rule. -/
theorem derives_singleton_to_terminals_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    (∃ B C : g.nt, ∃ u v : List T,
      w = u ++ v ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
        g.Derives [ISym.indexed B σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives [ISym.indexed C σ]
          (v.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
      σ = f :: ρ ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
        g.Derives [ISym.indexed B ρ]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ B : g.nt, ∃ f : g.flag,
      g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
        g.Derives [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ a : T,
      g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a]) := by
  rcases Relation.ReflTransGen.cases_head hder with hnil | ⟨mid, hstep, hrest⟩
  · cases w with
    | nil =>
        simp at hnil
    | cons a w =>
        simp at hnil
  · rcases transforms_kind_cases_of_isNormalForm hNF hstep with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨A₀, B, C, p, q, τ, _hB, _hC, hw₁, hw₂⟩
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
      subst p
      subst q
      subst A₀
      subst τ
      have hmid : mid = [ISym.indexed B σ, ISym.indexed C σ] := by
        simpa using hw₂
      subst mid
      rcases derives_pair_to_terminals_split (g := g) hrest with
        ⟨u, v, hw, hleft, hright⟩
      left
      exact ⟨B, C, u, v, hw, hstep, hleft, hright⟩
    · rcases hpop with ⟨A₀, B, f, p, q, ρ, _hB, hw₁, hw₂⟩
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hσ⟩
      subst p
      subst q
      subst A₀
      have hmid : mid = [ISym.indexed B ρ] := by
        simpa using hw₂
      subst mid
      right
      left
      exact ⟨f, ρ, B, hσ, hstep, hrest⟩
    · rcases hpush with ⟨A₀, B, f, p, q, τ, _hB, hw₁, hw₂⟩
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
      subst p
      subst q
      subst A₀
      subst τ
      have hmid : mid = [ISym.indexed B (f :: σ)] := by
        simpa using hw₂
      subst mid
      right
      right
      left
      exact ⟨B, f, hstep, hrest⟩
    · rcases hterm with ⟨A₀, a, p, q, τ, hw₁, hw₂⟩
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
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
      exact ⟨a, hstep, derives_terminal_singleton_eq (g := g) hrest⟩

/-- Exact recursive characterization of terminal derivations from one indexed nonterminal in
normal form. This is the simulator-facing form of first-step analysis: the forward direction
decomposes an accepting derivation, and the reverse direction composes the corresponding
subderivations after the exposed first step. -/
theorem derives_singleton_to_terminals_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T} :
    g.Derives [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ u v : List T,
        w = u ++ v ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
          g.Derives [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        σ = f :: ρ ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
          g.Derives [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag,
        g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
          g.Derives [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T,
        g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a]) := by
  constructor
  · exact derives_singleton_to_terminals_cases_of_isNormalForm hNF
  · intro h
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, u, v, hw, hstep, hleft, hright⟩
      subst w
      exact (deri_of_tran hstep).trans
        (derives_pair_to_terminals_of_derives (g := g) hleft hright)
    · rcases hpop with ⟨f, ρ, B, _hσ, hstep, hrest⟩
      exact (deri_of_tran hstep).trans hrest
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      exact (deri_of_tran hstep).trans hrest
    · rcases hterm with ⟨a, hstep, hw⟩
      subst w
      simpa using deri_of_tran hstep

/-- Recursive characterization of terminal derivations from one indexed nonterminal using
concrete normal-form rules from `g.rules`.

This is the structural, uncounted counterpart of
`derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm`: it exposes the first rule and the
subderivations generated by that rule, without hiding the rule choice behind `Transforms`. -/
theorem derives_singleton_to_terminals_rule_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T} :
    g.Derives [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          g.Derives [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          g.Derives [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        g.Derives [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a]) := by
  constructor
  · intro hder
    have hcases :=
      (derives_singleton_to_terminals_iff_of_isNormalForm
        (g := g) hNF (A := A) (σ := σ) (w := w)).mp hder
    rcases hcases with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, u, v, hw, hstep, hleft, hright⟩
      rcases (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, hσ, hstep, hrest⟩
      rcases (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mp
          (by simpa [hσ] using hstep) with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      rcases (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
    · rcases hterm with ⟨a, hstep, hw⟩
      rcases (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, hw⟩
  · intro h
    apply (derives_singleton_to_terminals_iff_of_isNormalForm
      (g := g) hNF (A := A) (σ := σ) (w := w)).mpr
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with
        ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hleft, hright⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] :=
        (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, u, v, hw, hstep, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] :=
        (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, hσ, by simpa [hσ] using hstep, hrest⟩
    · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] :=
        (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, hstep, hrest⟩
    · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.terminal a] :=
        (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, hstep, hw⟩

/-- Counted first-step analysis for a terminal derivation from one indexed nonterminal in
normal form. The binary case splits both the terminal word and the remaining step budget. -/
theorem derivesIn_singleton_to_terminals_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn (n + 1) [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
        g.DerivesIn m [ISym.indexed B σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k [ISym.indexed C σ]
          (v.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
      σ = f :: ρ ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
        g.DerivesIn n [ISym.indexed B ρ]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ B : g.nt, ∃ f : g.flag,
      g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ a : T,
      g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a] ∧ n = 0) := by
  have hsplitInput :
      g.DerivesIn (1 + n) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [Nat.add_comm] using hder
  rcases derivesIn_split (g := g) (m := 1) (n := n) hsplitInput with
    ⟨mid, hfirst, hrest⟩
  rcases hfirst with ⟨pre, hpre, hstep⟩
  have hpre' : [ISym.indexed A σ] = pre := by simpa using hpre
  subst pre
  rcases transforms_kind_cases_of_isNormalForm hNF hstep with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A₀, B, C, p, q, τ, _hB, _hC, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed B σ, ISym.indexed C σ] := by
      simpa using hw₂
    subst mid
    rcases derivesIn_pair_to_terminals_split (g := g) hrest with
      ⟨m, k, u, v, hmk, hw, hleft, hright⟩
    left
    exact ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
  · rcases hpop with ⟨A₀, B, f, p, q, ρ, _hB, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hσ⟩
    subst p
    subst q
    subst A₀
    have hmid : mid = [ISym.indexed B ρ] := by
      simpa using hw₂
    subst mid
    right
    left
    exact ⟨f, ρ, B, hσ, hstep, hrest⟩
  · rcases hpush with ⟨A₀, B, f, p, q, τ, _hB, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed B (f :: σ)] := by
      simpa using hw₂
    subst mid
    right
    right
    left
    exact ⟨B, f, hstep, hrest⟩
  · rcases hterm with ⟨A₀, a, p, q, τ, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
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
    exact ⟨a, hstep, derivesIn_terminal_singleton_eq (g := g) hrest,
      derivesIn_terminal_singleton_steps_eq_zero (g := g) hrest⟩

/-- Exact counted recursive characterization of terminal derivations from one indexed
nonterminal in normal form. -/
theorem derivesIn_singleton_to_terminals_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T} :
    g.DerivesIn (n + 1) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        m + k = n ∧
          w = u ++ v ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        σ = f :: ρ ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag,
        g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
          g.DerivesIn n [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T,
        g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a] ∧ n = 0) := by
  constructor
  · exact derivesIn_singleton_to_terminals_cases_of_isNormalForm hNF
  · intro h
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
      subst w
      have hpair :=
        derivesIn_pair_to_terminals_of_derivesIn (g := g) hleft hright
      have hpairn :
          g.DerivesIn n [ISym.indexed B σ, ISym.indexed C σ]
            ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
        simpa [hmk] using hpair
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hpairn
      simpa [Nat.add_comm] using htotal
    · rcases hpop with ⟨f, ρ, B, _hσ, hstep, hrest⟩
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hrest
      simpa [Nat.add_comm] using htotal
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hrest
      simpa [Nat.add_comm] using htotal
    · rcases hterm with ⟨a, hstep, hw, hn⟩
      subst w
      subst n
      simpa using derivesIn_one_of_transforms hstep

/-- Counted recursive characterization using concrete normal-form rules from `g.rules`.
This is the finite-search-facing form of singleton terminal derivability. -/
theorem derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T} :
    g.DerivesIn (n + 1) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          m + k = n ∧
          w = u ++ v ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a] ∧ n = 0) := by
  constructor
  · intro hder
    have hcases :=
      (derivesIn_singleton_to_terminals_iff_of_isNormalForm
        (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mp hder
    rcases hcases with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
      rcases (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, hσ, hstep, hrest⟩
      rcases (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mp
          (by simpa [hσ] using hstep) with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      rcases (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
    · rcases hterm with ⟨a, hstep, hw, hn⟩
      rcases (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
  · intro h
    apply (derivesIn_singleton_to_terminals_iff_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mpr
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with
        ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] :=
        (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] :=
        (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, hσ, by simpa [hσ] using hstep, hrest⟩
    · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] :=
        (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, hstep, hrest⟩
    · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.terminal a] :=
        (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, hstep, hw, hn⟩

theorem derives_singleton_to_terminals_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    0 < w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hder
  simp at hlen
  omega

theorem derives_singleton_to_terminals_length_pos_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    0 < w.length :=
  derives_singleton_to_terminals_length_pos_of_noEpsilon
    (g.noEpsilon_of_isNormalForm hNF) hder

theorem binary_subderivations_lengths_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {B C : g.nt} {σ : List g.flag} {u v : List T}
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    0 < u.length ∧ 0 < v.length :=
  ⟨derives_singleton_to_terminals_length_pos_of_noEpsilon hne hleft,
    derives_singleton_to_terminals_length_pos_of_noEpsilon hne hright⟩

theorem binary_subderivations_lengths_lt_parent_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {B C : g.nt} {σ : List g.flag} {w u v : List T}
    (hw : w = u ++ v)
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    u.length < w.length ∧ v.length < w.length := by
  have hpos := binary_subderivations_lengths_pos_of_noEpsilon hne hleft hright
  have hlen := congrArg List.length hw
  simp [List.length_append] at hlen
  omega

theorem binary_subderivations_lengths_lt_parent_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B C : g.nt} {σ : List g.flag} {w u v : List T}
    (hw : w = u ++ v)
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    u.length < w.length ∧ v.length < w.length :=
  binary_subderivations_lengths_lt_parent_of_noEpsilon
    (g.noEpsilon_of_isNormalForm hNF) hw hleft hright

/-- The two words generated by a binary branch are sublists of the parent word. -/
theorem binary_subderivation_words_sublist_parent {w u v : List T}
    (hw : w = u ++ v) :
    u.Sublist w ∧ v.Sublist w := by
  subst w
  exact ⟨List.sublist_append_left u v, List.sublist_append_right u v⟩

/-- Binary branch words remain inside any target word containing the parent as a sublist. -/
theorem binary_subderivation_words_sublist_target {w u v target : List T}
    (hw : w = u ++ v) (hwt : w.Sublist target) :
    u.Sublist target ∧ v.Sublist target := by
  have hparent := binary_subderivation_words_sublist_parent (T := T) hw
  exact ⟨hparent.1.trans hwt, hparent.2.trans hwt⟩

/-- Forward rule-level singleton decomposition with the binary branch annotated by the
well-founded facts needed for recursion on the target yield: both child yields are nonempty,
strictly shorter than the parent yield, and remain sublists of any ambient target containing
the parent yield. -/
theorem derives_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w target : List T}
    (hwt : w.Sublist target)
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
      (∃ B C : g.nt, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u.Sublist target ∧ v.Sublist target ∧
          g.Derives [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.Derives [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          g.Derives [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        g.Derives [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a]) := by
  have hcases :=
    (derives_singleton_to_terminals_rule_iff_of_isNormalForm
      (g := g) hNF (A := A) (σ := σ) (w := w)).mp hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hleft, hright⟩
    have hpos :=
      binary_subderivations_lengths_pos_of_noEpsilon
        (g.noEpsilon_of_isNormalForm hNF) hleft hright
    have hlt :=
      binary_subderivations_lengths_lt_parent_of_isNormalForm
        hNF hw hleft hright
    have hsub := binary_subderivation_words_sublist_target (T := T) hw hwt
    left
    exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
      hpos.1, hpos.2, hlt.1, hlt.2, hsub.1, hsub.2, hleft, hright⟩
  · right
    left
    exact hpop
  · right
    right
    left
    exact hpush
  · right
    right
    right
    exact hterm

/-- Counted forward rule-level singleton decomposition with explicit decreasing sub-budgets and
target-compatible child yields. This is the finite-search form of the first-step analysis: every
recursive premise has a strictly smaller counted budget, and binary premises also have nonempty,
strictly smaller terminal yields contained in the ambient target. -/
theorem derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w target : List T}
    (hwt : w.Sublist target)
    (hder : g.DerivesIn (n + 1) [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          m + k = n ∧
          m < n + 1 ∧ k < n + 1 ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u.Sublist target ∧ v.Sublist target ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          n < n + 1 ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        n < n + 1 ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a] ∧ n = 0) := by
  have hcases :=
    (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mp hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
    have hleftD := derives_of_derivesIn (g := g) hleft
    have hrightD := derives_of_derivesIn (g := g) hright
    have hpos :=
      binary_subderivations_lengths_pos_of_noEpsilon
        (g.noEpsilon_of_isNormalForm hNF) hleftD hrightD
    have hlt :=
      binary_subderivations_lengths_lt_parent_of_isNormalForm
        hNF hw hleftD hrightD
    have hsub := binary_subderivation_words_sublist_target (T := T) hw hwt
    have hm_lt : m < n + 1 := by omega
    have hk_lt : k < n + 1 := by omega
    left
    exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hm_lt, hk_lt, hw,
      hpos.1, hpos.2, hlt.1, hlt.2, hsub.1, hsub.2, hleft, hright⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, Nat.lt_succ_self n, hrest⟩
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
    right
    right
    left
    exact ⟨B, f, r, hr, hlhs, hc, hrhs, Nat.lt_succ_self n, hrest⟩
  · right
    right
    right
    exact hterm

theorem transformIsBinaryStep_nonterminalCount_increase {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsBinaryStep g w₁ w₂) :
    sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 := by
  rcases h with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsBinaryStep_terminalCount_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsBinaryStep g w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ := by
  rcases h with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]

theorem transformIsBinaryStep_stackHeight_eq_add {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsBinaryStep g w₁ w₂) :
    ∃ σ : List g.flag,
      sententialStackHeight w₂ = sententialStackHeight w₁ + σ.length := by
  rcases h with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
  refine ⟨σ, ?_⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsBinaryStep_maxStackHeight_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsBinaryStep g w₁ w₂) :
  sententialMaxStackHeight w₂ = sententialMaxStackHeight w₁ := by
  rcases h with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc, Nat.max_comm]

theorem transformIsPopStep_nonterminalCount_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPopStep g w₁ w₂) :
    sententialNonterminalCount w₂ = sententialNonterminalCount w₁ := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]

theorem transformIsPopStep_terminalCount_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPopStep g w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]

theorem transformIsPopStep_stackHeight_decrease_one {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPopStep g w₁ w₂) :
    sententialStackHeight w₁ = sententialStackHeight w₂ + 1 := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsPopStep_maxStackHeight_le {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPopStep g w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_pop_le (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

theorem transformIsPushStep_nonterminalCount_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPushStep g w₁ w₂) :
    sententialNonterminalCount w₂ = sententialNonterminalCount w₁ := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]

theorem transformIsPushStep_terminalCount_eq {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPushStep g w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]

theorem transformIsPushStep_stackHeight_increase_one {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPushStep g w₁ w₂) :
    sententialStackHeight w₂ = sententialStackHeight w₁ + 1 := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsPushStep_maxStackHeight_le_succ {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsPushStep g w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ + 1 := by
  rcases h with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_push_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

theorem transformIsTerminalStep_nonterminalCount_decrease {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsTerminalStep g w₁ w₂) :
    sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsTerminalStep_terminalCount_increase {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsTerminalStep g w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsTerminalStep_stackHeight_eq_add {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsTerminalStep g w₁ w₂) :
    ∃ σ : List g.flag,
      sententialStackHeight w₁ = sententialStackHeight w₂ + σ.length := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  refine ⟨σ, ?_⟩
  rw [hw₁, hw₂]
  simp [List.append_assoc]
  omega

theorem transformIsTerminalStep_maxStackHeight_le {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsTerminalStep g w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  rw [hw₁, hw₂]
  simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
    max_drop_middle_le (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

theorem transformIsTerminalStep_stackHeightDecrease_le_maxStackHeight {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : TransformIsTerminalStep g w₁ w₂) :
    sententialStackHeight w₁ - sententialStackHeight w₂ ≤
      sententialMaxStackHeight w₁ := by
  rcases h with ⟨A, a, u, v, σ, hw₁, hw₂⟩
  have hdiff :
      sententialStackHeight w₁ - sententialStackHeight w₂ = σ.length := by
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega
  have hσ :
      σ.length ≤ sententialMaxStackHeight w₁ := by
    rw [hw₁]
    simp only [sententialMaxStackHeight_append, sententialMaxStackHeight_indexed]
    omega
  rw [hdiff]
  exact hσ

theorem transforms_binaryStep_iff_nonterminalCount_increase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsBinaryStep g w₁ w₂ ↔
      sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 := by
  constructor
  · exact transformIsBinaryStep_nonterminalCount_increase
  · intro hinc
    rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
    · exact hbin
    · have hsame := transformIsPopStep_nonterminalCount_eq hpop
      omega
    · have hsame := transformIsPushStep_nonterminalCount_eq hpush
      omega
    · have hdec := transformIsTerminalStep_nonterminalCount_decrease hterm
      omega

theorem transforms_terminalStep_iff_terminalCount_increase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsTerminalStep g w₁ w₂ ↔
      sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
  constructor
  · exact transformIsTerminalStep_terminalCount_increase
  · intro hinc
    rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
    · have hsame := transformIsBinaryStep_terminalCount_eq hbin
      omega
    · have hsame := transformIsPopStep_terminalCount_eq hpop
      omega
    · have hsame := transformIsPushStep_terminalCount_eq hpush
      omega
    · exact hterm

theorem traceTerminalEraseStackHeight_le_terminalIncreaseCount_mul_of_isDerivationTrace_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B) :
    traceTerminalEraseStackHeight trace ≤ traceTerminalIncreaseCount trace * B := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have htailBound :
              ∀ x ∈ (w₂ :: rest), sententialMaxStackHeight x ≤ B := by
            intro x hx
            exact hbound x (by simp [hx])
          have htail := ih htrace.2 htailBound
          by_cases htermCount : sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1
          · have htermStep :
                TransformIsTerminalStep g w₁ w₂ :=
              (transforms_terminalStep_iff_terminalCount_increase_of_isNormalForm
                hNF htrace.1).mpr htermCount
            have hstepMax :
                sententialStackHeight w₁ - sententialStackHeight w₂ ≤ B :=
              le_trans
                (transformIsTerminalStep_stackHeightDecrease_le_maxStackHeight htermStep)
                (hbound w₁ (by simp))
            simp only [traceTerminalEraseStackHeight_cons_cons,
              traceTerminalIncreaseCount_cons_cons, if_pos htermCount]
            calc
              (sententialStackHeight w₁ - sententialStackHeight w₂) +
                  traceTerminalEraseStackHeight (w₂ :: rest)
                  ≤ B + traceTerminalIncreaseCount (w₂ :: rest) * B :=
                    Nat.add_le_add hstepMax htail
              _ = (1 + traceTerminalIncreaseCount (w₂ :: rest)) * B := by
                    rw [Nat.add_mul, Nat.one_mul]
          · simp only [traceTerminalEraseStackHeight_cons_cons,
              traceTerminalIncreaseCount_cons_cons, if_neg htermCount]
            simpa using htail

theorem transforms_popStep_iff_counts_and_stackHeight_decrease_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsPopStep g w₁ w₂ ↔
      sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∧
        sententialTerminalCount w₂ = sententialTerminalCount w₁ ∧
        sententialStackHeight w₁ = sententialStackHeight w₂ + 1 := by
  constructor
  · intro hpop
    exact ⟨transformIsPopStep_nonterminalCount_eq hpop,
      transformIsPopStep_terminalCount_eq hpop,
      transformIsPopStep_stackHeight_decrease_one hpop⟩
  · rintro ⟨hnt, htermCount, hstack⟩
    rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
    · have hinc := transformIsBinaryStep_nonterminalCount_increase hbin
      omega
    · exact hpop
    · have hpushStack := transformIsPushStep_stackHeight_increase_one hpush
      omega
    · have htermInc := transformIsTerminalStep_terminalCount_increase hterm
      omega

theorem transforms_pushStep_iff_counts_and_stackHeight_increase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsPushStep g w₁ w₂ ↔
      sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∧
        sententialTerminalCount w₂ = sententialTerminalCount w₁ ∧
        sententialStackHeight w₂ = sententialStackHeight w₁ + 1 := by
  constructor
  · intro hpush
    exact ⟨transformIsPushStep_nonterminalCount_eq hpush,
      transformIsPushStep_terminalCount_eq hpush,
      transformIsPushStep_stackHeight_increase_one hpush⟩
  · rintro ⟨hnt, htermCount, hstack⟩
    rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
    · have hinc := transformIsBinaryStep_nonterminalCount_increase hbin
      omega
    · have hpopStack := transformIsPopStep_stackHeight_decrease_one hpop
      omega
    · exact hpush
    · have htermInc := transformIsTerminalStep_terminalCount_increase hterm
      omega

theorem transforms_pushStep_iff_observablePush_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsPushStep g w₁ w₂ ↔ TransformIsObservablePush w₁ w₂ := by
  simpa [TransformIsObservablePush] using
    transforms_pushStep_iff_counts_and_stackHeight_increase_of_isNormalForm hNF h

theorem transforms_popStep_iff_observablePop_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsPopStep g w₁ w₂ ↔ TransformIsObservablePop w₁ w₂ := by
  simpa [TransformIsObservablePop] using
    transforms_popStep_iff_counts_and_stackHeight_decrease_of_isNormalForm hNF h

theorem transforms_maxStackHeight_le_add_pushIndicator_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialMaxStackHeight w₂ ≤
      sententialMaxStackHeight w₁ + if TransformIsObservablePush w₁ w₂ then 1 else 0 := by
  by_cases hpushObs : TransformIsObservablePush w₁ w₂
  · have hpush :=
      (transforms_pushStep_iff_observablePush_of_isNormalForm hNF h).mpr hpushObs
    rw [if_pos hpushObs]
    exact transformIsPushStep_maxStackHeight_le_succ hpush
  · rw [if_neg hpushObs]
    rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
    · have hmax := transformIsBinaryStep_maxStackHeight_eq hbin
      omega
    · exact transformIsPopStep_maxStackHeight_le hpop
    · have hobs :=
        (transforms_pushStep_iff_observablePush_of_isNormalForm hNF h).mp hpush
      exact False.elim (hpushObs hobs)
    · exact transformIsTerminalStep_maxStackHeight_le hterm

theorem transforms_stackHeightIncrease_eq_push_add_binaryCopy_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialStackHeight w₂ - sententialStackHeight w₁ =
      (if TransformIsObservablePush w₁ w₂ then 1 else 0) +
        (if sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 then
          sententialStackHeight w₂ - sententialStackHeight w₁
        else
          0) := by
  rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · have hnt := transformIsBinaryStep_nonterminalCount_increase hbin
    have htermCount := transformIsBinaryStep_terminalCount_eq hbin
    have hstack := transformIsBinaryStep_stackHeight_eq_add hbin
    have hpushObs : ¬ TransformIsObservablePush w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨hntEq, _, _⟩
      omega
    rcases hstack with ⟨σ, hstack⟩
    simp [hpushObs, hnt]
  · have hnt := transformIsPopStep_nonterminalCount_eq hpop
    have htermCount := transformIsPopStep_terminalCount_eq hpop
    have hstack := transformIsPopStep_stackHeight_decrease_one hpop
    have hpushObs : ¬ TransformIsObservablePush w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨_, _, hpushStack⟩
      omega
    have hntInc :
        ¬ sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 := by
      omega
    simp [hpushObs, hntInc]
    omega
  · have hnt := transformIsPushStep_nonterminalCount_eq hpush
    have hstack := transformIsPushStep_stackHeight_increase_one hpush
    have hpushObs :
        TransformIsObservablePush w₁ w₂ :=
      (transforms_pushStep_iff_observablePush_of_isNormalForm hNF h).mp hpush
    have hntInc :
        ¬ sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 := by
      omega
    simp [hpushObs, hntInc]
    omega
  · have hntDec := transformIsTerminalStep_nonterminalCount_decrease hterm
    have htermInc := transformIsTerminalStep_terminalCount_increase hterm
    have hstack := transformIsTerminalStep_stackHeight_eq_add hterm
    have hpushObs : ¬ TransformIsObservablePush w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨hnt, _, _⟩
      omega
    have hntInc :
        ¬ sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 := by
      omega
    rcases hstack with ⟨σ, hstack⟩
    simp [hpushObs, hntInc]
    omega

theorem transforms_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialStackHeight w₁ - sententialStackHeight w₂ =
      (if TransformIsObservablePop w₁ w₂ then 1 else 0) +
        (if sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 then
          sententialStackHeight w₁ - sententialStackHeight w₂
        else
          0) := by
  rcases transforms_kind_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · have hnt := transformIsBinaryStep_nonterminalCount_increase hbin
    have htermCount := transformIsBinaryStep_terminalCount_eq hbin
    have hstack := transformIsBinaryStep_stackHeight_eq_add hbin
    have hpopObs : ¬ TransformIsObservablePop w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨hntEq, _, _⟩
      omega
    have htermInc :
        ¬ sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
      omega
    rcases hstack with ⟨σ, hstack⟩
    simp [hpopObs, htermInc]
    omega
  · have htermCount := transformIsPopStep_terminalCount_eq hpop
    have hstack := transformIsPopStep_stackHeight_decrease_one hpop
    have hpopObs :
        TransformIsObservablePop w₁ w₂ :=
      (transforms_popStep_iff_observablePop_of_isNormalForm hNF h).mp hpop
    have htermInc :
        ¬ sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
      omega
    simp [hpopObs, htermInc]
    omega
  · have hnt := transformIsPushStep_nonterminalCount_eq hpush
    have htermCount := transformIsPushStep_terminalCount_eq hpush
    have hstack := transformIsPushStep_stackHeight_increase_one hpush
    have hpopObs : ¬ TransformIsObservablePop w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨_, _, hpopStack⟩
      omega
    have htermInc :
        ¬ sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
      omega
    simp [hpopObs, htermInc]
    omega
  · have htermInc := transformIsTerminalStep_terminalCount_increase hterm
    have hstack := transformIsTerminalStep_stackHeight_eq_add hterm
    have hpopObs : ¬ TransformIsObservablePop w₁ w₂ := by
      intro hobs
      rcases hobs with ⟨_, htermCount, _⟩
      omega
    rcases hstack with ⟨σ, hstack⟩
    simp [hpopObs, htermInc]

theorem isDerivationTrace_stackHeightIncrease_eq_push_add_binaryCopy_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) :
    traceStackHeightIncrease trace =
      tracePushStepCount trace + traceBinaryCopyStackHeight trace := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have hstep :=
            transforms_stackHeightIncrease_eq_push_add_binaryCopy_of_isNormalForm
              hNF htrace.1
          have htail := ih htrace.2
          simp only [traceStackHeightIncrease_cons_cons, tracePushStepCount_cons_cons,
            traceBinaryCopyStackHeight_cons_cons]
          rw [htail]
          omega

theorem isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) :
    traceStackHeightDecrease trace =
      tracePopStepCount trace + traceTerminalEraseStackHeight trace := by
  induction trace with
  | nil =>
      simp
  | cons w₁ trace ih =>
      cases trace with
      | nil =>
          simp
      | cons w₂ rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have hstep :=
            transforms_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
              hNF htrace.1
          have htail := ih htrace.2
          simp only [traceStackHeightDecrease_cons_cons, tracePopStepCount_cons_cons,
            traceTerminalEraseStackHeight_cons_cons]
          rw [htail]
          omega

theorem accepting_derivationTrace_push_add_binaryCopy_eq_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    tracePushStepCount trace + traceBinaryCopyStackHeight trace =
      tracePopStepCount trace + traceTerminalEraseStackHeight trace := by
  have hinc :=
    isDerivationTrace_stackHeightIncrease_eq_push_add_binaryCopy_of_isNormalForm
      hNF htrace
  have hdec :=
    isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
      hNF htrace
  have hbalance :=
    accepting_derivationTrace_stackHeightIncrease_eq_decrease (g := g) hhead hlast
  omega

theorem accepting_derivationTrace_suffix_stackHeight_add_push_add_binaryCopy_eq_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialStackHeight (trace.get ⟨i, hi⟩) +
        tracePushStepCount (trace.drop i) +
        traceBinaryCopyStackHeight (trace.drop i) =
      tracePopStepCount (trace.drop i) +
        traceTerminalEraseStackHeight (trace.drop i) := by
  have hdropTrace := isDerivationTrace_drop htrace i
  have hheadDrop := trace_drop_head?_eq_get (g := g) hi
  have hlastDrop : (trace.drop i).getLast? = some (w.map ISym.terminal) := by
    rw [trace_drop_getLast?_eq_getLast? (g := g) hi, hlast]
  have hbalance :=
    traceStackHeight_balance (g := g) hheadDrop hlastDrop
  have hbalance' :
      traceStackHeightDecrease (trace.drop i) =
        sententialStackHeight (trace.get ⟨i, hi⟩) +
          traceStackHeightIncrease (trace.drop i) := by
    simpa using hbalance
  have hinc :=
    isDerivationTrace_stackHeightIncrease_eq_push_add_binaryCopy_of_isNormalForm
      hNF hdropTrace
  have hdec :=
    isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
      hNF hdropTrace
  omega

theorem accepting_derivationTrace_get_maxStackHeight_le_future_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePopStepCount (trace.drop i) +
        traceTerminalEraseStackHeight (trace.drop i) := by
  have hheight :=
    accepting_derivationTrace_get_maxStackHeight_le_future_decrease
      (g := g) hlast hi
  have hdropTrace := isDerivationTrace_drop htrace i
  have hdec :=
    isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
      hNF hdropTrace
  omega

theorem accepting_derivationTrace_get_sententialStackHeight_le_future_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePopStepCount (trace.drop i) +
        traceTerminalEraseStackHeight (trace.drop i) := by
  have hheight :=
    accepting_derivationTrace_get_stackHeight_le_future_decrease
      (g := g) hlast hi
  have hdropTrace := isDerivationTrace_drop htrace i
  have hdec :=
    isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
      hNF hdropTrace
  omega

theorem accepting_derivationTrace_get_encodeSentential_length_le_future_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
      w.length + w.length +
        (tracePopStepCount (trace.drop i) +
          traceTerminalEraseStackHeight (trace.drop i)) := by
  rw [encodeSentential_length]
  have hlen :
      (trace.get ⟨i, hi⟩).length ≤ w.length := by
    have hsuffix := isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
    have hlen :=
      derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix
    simpa using hlen
  have hnt :
      sententialNonterminalCount (trace.get ⟨i, hi⟩) ≤ w.length :=
    le_trans (sententialNonterminalCount_le_length _) hlen
  have hstack :
      sententialStackHeight (trace.get ⟨i, hi⟩) ≤
        tracePopStepCount (trace.drop i) +
          traceTerminalEraseStackHeight (trace.drop i) :=
    accepting_derivationTrace_get_sententialStackHeight_le_future_pop_add_terminalErase_of_isNormalForm
      hNF htrace hlast hi
  omega

/-- A normal-form step either increases the number of nonterminals by one, preserves it, or
decreases it by one. -/
theorem transforms_nonterminalCount_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 ∨
      sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∨
      sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    right
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    right
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    right
    right
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega

/-- A normal-form step either preserves the number of terminals or increases it by one. -/
theorem transforms_terminalCount_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ ∨
      sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    right
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega

theorem transforms_terminalCount_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₂ ≤ sententialTerminalCount w₁ + 1 := by
  rcases transforms_terminalCount_cases_of_isNormalForm hNF h with htc | htc <;> omega

theorem transforms_terminalCount_succ_iff_nonterminalCount_decrease_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 ↔
      sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    constructor <;> intro _ <;> omega

/-- A normal-form step can increase the maximum stack height by at most one. -/
theorem transforms_maxStackHeight_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc, Nat.max_comm]
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_pop_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_push_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_terminal_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

/-- In a counted normal-form derivation, sentential-form length grows by at most the number of
steps. -/
theorem derivesIn_length_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    w₂.length ≤ w₁.length + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_len := ih hprev
      have hstep_len := transforms_length_le_succ_of_isNormalForm hNF hstep
      omega

/-- In a counted normal-form derivation, the terminal count grows by at most the number of
steps. -/
theorem derivesIn_terminalCount_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    sententialTerminalCount w₂ ≤ sententialTerminalCount w₁ + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_term := ih hprev
      have hstep_term := transforms_terminalCount_le_succ_of_isNormalForm hNF hstep
      omega

/-- In a counted normal-form derivation, the maximum stack height grows by at most the number
of steps. -/
theorem derivesIn_maxStackHeight_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_height := ih hprev
      have hstep_height := transforms_maxStackHeight_le_succ_of_isNormalForm hNF hstep
      omega

/-- A counted accepting normal-form derivation for a word of length `k` uses at least `k`
steps. -/
theorem generated_length_le_derivesIn_steps_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal)) :
    w.length ≤ n := by
  have hterm := derivesIn_terminalCount_le_add_of_isNormalForm hNF h
  simpa using hterm

theorem isDerivationTrace_terminalCount_eq_head_add_terminalIncreaseCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first last : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hlast : trace.getLast? = some last) :
    sententialTerminalCount last =
      sententialTerminalCount first + traceTerminalIncreaseCount trace := by
  induction trace generalizing first last with
  | nil =>
      simp at hhead
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hhead hlast
          subst first
          subst last
          simp
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have hhead_tail : (b :: rest).head? = some b := by simp
          have hlast_tail : (b :: rest).getLast? = some last := by
            simpa using hlast
          have ih_tail :=
            ih htrace.2 hhead_tail hlast_tail
          have hfirst : a = first := by simpa using hhead
          subst first
          rcases transforms_terminalCount_cases_of_isNormalForm hNF htrace.1 with hpreserve | hinc
          · have hnot :
                ¬ sententialTerminalCount b = sententialTerminalCount a + 1 := by
              omega
            rw [traceTerminalIncreaseCount_cons_cons, if_neg hnot]
            omega
          · rw [traceTerminalIncreaseCount_cons_cons, if_pos hinc]
            omega

theorem isDerivationTrace_nonterminal_balance_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first last : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    (hlast : trace.getLast? = some last) :
    sententialNonterminalCount last + traceNonterminalDecreaseCount trace =
      sententialNonterminalCount first + traceNonterminalIncreaseCount trace := by
  induction trace generalizing first last with
  | nil =>
      simp at hhead
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hhead hlast
          subst first
          subst last
          simp
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have hhead_tail : (b :: rest).head? = some b := by simp
          have hlast_tail : (b :: rest).getLast? = some last := by
            simpa using hlast
          have ih_tail :=
            ih htrace.2 hhead_tail hlast_tail
          have hfirst : a = first := by simpa using hhead
          subst first
          rcases transforms_nonterminalCount_cases_of_isNormalForm hNF htrace.1 with hinc | hsame | hdec
          · have hnot_dec :
                ¬ sententialNonterminalCount a = sententialNonterminalCount b + 1 := by
              omega
            rw [traceNonterminalIncreaseCount_cons_cons, traceNonterminalDecreaseCount_cons_cons,
              if_pos hinc, if_neg hnot_dec]
            omega
          · have hnot_inc :
                ¬ sententialNonterminalCount b = sententialNonterminalCount a + 1 := by
              omega
            have hnot_dec :
                ¬ sententialNonterminalCount a = sententialNonterminalCount b + 1 := by
              omega
            rw [traceNonterminalIncreaseCount_cons_cons, traceNonterminalDecreaseCount_cons_cons,
              if_neg hnot_inc, if_neg hnot_dec]
            omega
          · have hnot_inc :
                ¬ sententialNonterminalCount b = sententialNonterminalCount a + 1 := by
              omega
            rw [traceNonterminalIncreaseCount_cons_cons, traceNonterminalDecreaseCount_cons_cons,
              if_neg hnot_inc, if_pos hdec]
            omega

theorem isDerivationTrace_get_terminalCount_eq_head_add_terminalIncreaseCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ} (hi : i < trace.length) :
    sententialTerminalCount (trace.get ⟨i, hi⟩) =
      sententialTerminalCount first + traceTerminalIncreaseCountUpTo i trace := by
  induction i generalizing trace first with
  | zero =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          have hfirst : a = first := by simpa using hhead
          subst first
          simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hi
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have hi_tail : i < (b :: rest).length := by simpa using hi
              have hget :
                  (a :: b :: rest).get ⟨i + 1, hi⟩ =
                    (b :: rest).get ⟨i, hi_tail⟩ := by
                simp
              have ih_tail :=
                ih (trace := b :: rest) (first := b) htrace.2 (by simp) hi_tail
              have hfirst : a = first := by simpa using hhead
              subst first
              rcases transforms_terminalCount_cases_of_isNormalForm hNF htrace.1 with
                hpreserve | hinc
              · have hnot :
                    ¬ sententialTerminalCount b = sententialTerminalCount a + 1 := by
                  omega
                rw [traceTerminalIncreaseCountUpTo_succ_cons_cons, if_neg hnot]
                simp only [Nat.zero_add]
                rw [hget, ih_tail]
                omega
              · rw [traceTerminalIncreaseCountUpTo_succ_cons_cons, if_pos hinc]
                rw [hget, ih_tail]
                omega

theorem isDerivationTrace_get_nonterminal_balanceUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ} (hi : i < trace.length) :
    sententialNonterminalCount (trace.get ⟨i, hi⟩) +
        traceNonterminalDecreaseCountUpTo i trace =
      sententialNonterminalCount first + traceNonterminalIncreaseCountUpTo i trace := by
  induction i generalizing trace first with
  | zero =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          have hfirst : a = first := by simpa using hhead
          subst first
          simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hi
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have hi_tail : i < (b :: rest).length := by simpa using hi
              have hget :
                  (a :: b :: rest).get ⟨i + 1, hi⟩ =
                    (b :: rest).get ⟨i, hi_tail⟩ := by
                simp
              have ih_tail :=
                ih (trace := b :: rest) (first := b) htrace.2 (by simp) hi_tail
              have hfirst : a = first := by simpa using hhead
              subst first
              rcases transforms_nonterminalCount_cases_of_isNormalForm hNF htrace.1 with
                hinc | hsame | hdec
              · have hnot_dec :
                    ¬ sententialNonterminalCount a =
                      sententialNonterminalCount b + 1 := by
                  omega
                rw [traceNonterminalIncreaseCountUpTo_succ_cons_cons,
                  traceNonterminalDecreaseCountUpTo_succ_cons_cons,
                  if_pos hinc, if_neg hnot_dec]
                simp only [Nat.zero_add]
                rw [hget, ih_tail]
                omega
              · have hnot_inc :
                    ¬ sententialNonterminalCount b =
                      sententialNonterminalCount a + 1 := by
                  omega
                have hnot_dec :
                    ¬ sententialNonterminalCount a =
                      sententialNonterminalCount b + 1 := by
                  omega
                rw [traceNonterminalIncreaseCountUpTo_succ_cons_cons,
                  traceNonterminalDecreaseCountUpTo_succ_cons_cons,
                  if_neg hnot_inc, if_neg hnot_dec]
                simp only [Nat.zero_add]
                rw [hget, ih_tail]
                omega
              · have hnot_inc :
                    ¬ sententialNonterminalCount b =
                      sententialNonterminalCount a + 1 := by
                  omega
                rw [traceNonterminalIncreaseCountUpTo_succ_cons_cons,
                  traceNonterminalDecreaseCountUpTo_succ_cons_cons,
                  if_neg hnot_inc, if_pos hdec]
                simp only [Nat.zero_add]
                rw [hget]
                have := ih_tail
                omega

theorem isDerivationTrace_terminalIncreaseCount_eq_nonterminalDecreaseCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) :
    traceTerminalIncreaseCount trace = traceNonterminalDecreaseCount trace := by
  induction trace with
  | nil =>
      simp
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          have ih_tail := ih htrace.2
          have hiff :=
            transforms_terminalCount_succ_iff_nonterminalCount_decrease_of_isNormalForm
              hNF htrace.1
          by_cases hterm :
              sententialTerminalCount b = sententialTerminalCount a + 1
          · have hdec :
                sententialNonterminalCount a = sententialNonterminalCount b + 1 :=
              hiff.mp hterm
            simp [traceTerminalIncreaseCount, traceNonterminalDecreaseCount, hterm, hdec,
              ih_tail]
          · have hdec :
                ¬ sententialNonterminalCount a = sententialNonterminalCount b + 1 := by
              intro h
              exact hterm (hiff.mpr h)
            simp [traceTerminalIncreaseCount, traceNonterminalDecreaseCount, hterm, hdec,
              ih_tail]

theorem isDerivationTrace_terminalIncreaseCountUpTo_eq_nonterminalDecreaseCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) (i : ℕ) :
    traceTerminalIncreaseCountUpTo i trace =
      traceNonterminalDecreaseCountUpTo i trace := by
  induction i generalizing trace with
  | zero =>
      simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp
      | cons a rest =>
          cases rest with
          | nil =>
              simp
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have ih_tail := ih htrace.2
              have hiff :=
                transforms_terminalCount_succ_iff_nonterminalCount_decrease_of_isNormalForm
                  hNF htrace.1
              by_cases hterm :
                  sententialTerminalCount b = sententialTerminalCount a + 1
              · have hdec :
                    sententialNonterminalCount a = sententialNonterminalCount b + 1 :=
                  hiff.mp hterm
                simp [traceTerminalIncreaseCountUpTo, traceNonterminalDecreaseCountUpTo,
                  hterm, hdec, ih_tail]
              · have hdec :
                    ¬ sententialNonterminalCount a = sententialNonterminalCount b + 1 := by
                  intro h
                  exact hterm (hiff.mpr h)
                simp [traceTerminalIncreaseCountUpTo, traceNonterminalDecreaseCountUpTo,
                  hterm, hdec, ih_tail]

theorem accepting_derivationTrace_terminalIncreaseCount_eq_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceTerminalIncreaseCount trace = w.length := by
  have hcount :=
    isDerivationTrace_terminalCount_eq_head_add_terminalIncreaseCount_of_isNormalForm
      hNF htrace hhead hlast
  simpa using hcount.symm

theorem accepting_derivationTrace_nonterminalDecreaseCount_eq_succ_nonterminalIncreaseCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceNonterminalDecreaseCount trace =
      traceNonterminalIncreaseCount trace + 1 := by
  have hbalance :=
    isDerivationTrace_nonterminal_balance_of_isNormalForm
      hNF htrace hhead hlast
  have hbalance' :
      traceNonterminalDecreaseCount trace =
        1 + traceNonterminalIncreaseCount trace := by
    simpa using hbalance
  omega

theorem accepting_derivationTrace_nonterminalIncreaseCount_succ_eq_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceNonterminalIncreaseCount trace + 1 = w.length := by
  have hterm :=
    accepting_derivationTrace_terminalIncreaseCount_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast
  have hterm_dec :=
    isDerivationTrace_terminalIncreaseCount_eq_nonterminalDecreaseCount_of_isNormalForm
      hNF htrace
  have hdec :=
    accepting_derivationTrace_nonterminalDecreaseCount_eq_succ_nonterminalIncreaseCount_of_isNormalForm
      hNF htrace hhead hlast
  omega

theorem derivationTrace_suffix_terminalCount_add_increase_eq_last_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {last : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some last)
    {i : ℕ} (hi : i < trace.length) :
    sententialTerminalCount (trace.get ⟨i, hi⟩) +
        traceTerminalIncreaseCount (trace.drop i) =
      sententialTerminalCount last := by
  have hdropTrace := isDerivationTrace_drop htrace i
  have hheadDrop := trace_drop_head?_eq_get (g := g) hi
  have hlastDrop : (trace.drop i).getLast? = some last := by
    rw [trace_drop_getLast?_eq_getLast? (g := g) hi, hlast]
  have hcount :=
    isDerivationTrace_terminalCount_eq_head_add_terminalIncreaseCount_of_isNormalForm
      hNF hdropTrace hheadDrop hlastDrop
  omega

theorem accepting_derivationTrace_suffix_terminalCount_add_increase_eq_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialTerminalCount (trace.get ⟨i, hi⟩) +
        traceTerminalIncreaseCount (trace.drop i) =
      w.length := by
  have h :=
    derivationTrace_suffix_terminalCount_add_increase_eq_last_of_isNormalForm
      (g := g) hNF htrace hlast hi
  simpa using h

theorem accepting_derivationTrace_suffix_terminalIncreaseCount_le_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    traceTerminalIncreaseCount (trace.drop i) ≤ w.length := by
  have h :=
    accepting_derivationTrace_suffix_terminalCount_add_increase_eq_target_length_of_isNormalForm
      (g := g) hNF htrace hlast hi
  omega

theorem accepting_derivationTrace_suffix_terminalEraseStackHeight_le_target_length_mul_stackBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    traceTerminalEraseStackHeight (trace.drop i) ≤ w.length * B := by
  have hdropTrace := isDerivationTrace_drop htrace i
  have hdropBound :
      ∀ x ∈ trace.drop i, sententialMaxStackHeight x ≤ B := by
    intro x hx
    exact hbound x (List.mem_of_mem_drop hx)
  have herase :=
    traceTerminalEraseStackHeight_le_terminalIncreaseCount_mul_of_isDerivationTrace_stackBound
      (g := g) hNF hdropTrace hdropBound
  have hterm :=
    accepting_derivationTrace_suffix_terminalIncreaseCount_le_target_length_of_isNormalForm
      (g := g) hNF htrace hlast hi
  exact le_trans herase (Nat.mul_le_mul_right B hterm)

theorem accepting_derivationTrace_get_sententialStackHeight_le_future_pop_add_target_mul_stackBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    sententialStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePopStepCount (trace.drop i) + w.length * B := by
  have hlive :=
    accepting_derivationTrace_get_sententialStackHeight_le_future_pop_add_terminalErase_of_isNormalForm
      (g := g) hNF htrace hlast hi
  have herase :=
    accepting_derivationTrace_suffix_terminalEraseStackHeight_le_target_length_mul_stackBound_of_isNormalForm
      (g := g) hNF htrace hlast hbound hi
  omega

theorem accepting_derivationTrace_get_encodeSentential_length_le_future_pop_add_target_mul_stackBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
      w.length + w.length +
        (tracePopStepCount (trace.drop i) + w.length * B) := by
  rw [encodeSentential_length]
  have hlen :
      (trace.get ⟨i, hi⟩).length ≤ w.length := by
    have hsuffix := isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
    have hlen :=
      derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix
    simpa using hlen
  have hnt :
      sententialNonterminalCount (trace.get ⟨i, hi⟩) ≤ w.length :=
    le_trans (sententialNonterminalCount_le_length _) hlen
  have hstack :
      sententialStackHeight (trace.get ⟨i, hi⟩) ≤
        tracePopStepCount (trace.drop i) + w.length * B :=
    accepting_derivationTrace_get_sententialStackHeight_le_future_pop_add_target_mul_stackBound_of_isNormalForm
      (g := g) hNF htrace hlast hbound hi
  omega

theorem accepting_derivationTrace_get_encodeSentential_length_le_popBudget_add_target_mul_stackBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
      w.length + w.length + (P + w.length * B) := by
  have hfuture :=
    accepting_derivationTrace_get_encodeSentential_length_le_future_pop_add_target_mul_stackBound_of_isNormalForm
      (g := g) hNF htrace hlast hbound hi
  have hdrop := tracePopStepCount_drop_le (g := g) i trace
  omega

theorem accepting_derivationTrace_get_encodeSentential_length_le_popBudget_stackBound_lengthBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
      L + L + (P + L * B) := by
  have hbase :=
    accepting_derivationTrace_get_encodeSentential_length_le_popBudget_add_target_mul_stackBound_of_isNormalForm
      (g := g) hNF htrace hlast hbound hpop hi
  have hmul : w.length * B ≤ L * B := Nat.mul_le_mul_right B hwlen
  omega

theorem accepting_derivationTrace_get_encodeSentential_length_le_stepBudget_stackBound_lengthBound_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L n N : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hnN : n ≤ N)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤
      L + L + (N + L * B) := by
  have hpop : tracePopStepCount trace ≤ N :=
    le_trans (tracePopStepCount_le_steps_of_length_eq (g := g) hlen) hnN
  exact
    accepting_derivationTrace_get_encodeSentential_length_le_popBudget_stackBound_lengthBound_of_isNormalForm
      (g := g) (B := B) (L := L) (P := N)
      hNF htrace hlast hwlen hbound hpop hi

theorem derivationTrace_suffix_nonterminal_balance_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {last : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some last)
    {i : ℕ} (hi : i < trace.length) :
    sententialNonterminalCount last +
        traceNonterminalDecreaseCount (trace.drop i) =
      sententialNonterminalCount (trace.get ⟨i, hi⟩) +
        traceNonterminalIncreaseCount (trace.drop i) := by
  have hdropTrace := isDerivationTrace_drop htrace i
  have hheadDrop := trace_drop_head?_eq_get (g := g) hi
  have hlastDrop : (trace.drop i).getLast? = some last := by
    rw [trace_drop_getLast?_eq_getLast? (g := g) hi, hlast]
  exact isDerivationTrace_nonterminal_balance_of_isNormalForm
    hNF hdropTrace hheadDrop hlastDrop

theorem accepting_derivationTrace_suffix_nonterminalDecreaseCount_eq_terminalIncreaseCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) (i : ℕ) :
    traceNonterminalDecreaseCount (trace.drop i) =
      traceTerminalIncreaseCount (trace.drop i) := by
  have hdropTrace := isDerivationTrace_drop htrace i
  exact (isDerivationTrace_terminalIncreaseCount_eq_nonterminalDecreaseCount_of_isNormalForm
    hNF hdropTrace).symm

theorem accepting_derivationTrace_suffix_nonterminalCount_add_increase_eq_terminalIncreaseCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialNonterminalCount (trace.get ⟨i, hi⟩) +
        traceNonterminalIncreaseCount (trace.drop i) =
      traceTerminalIncreaseCount (trace.drop i) := by
  have hbalance :=
    derivationTrace_suffix_nonterminal_balance_of_isNormalForm
      (g := g) hNF htrace hlast hi
  have hdec :=
    accepting_derivationTrace_suffix_nonterminalDecreaseCount_eq_terminalIncreaseCount_of_isNormalForm
      (g := g) hNF htrace i
  simpa [hdec] using hbalance.symm

theorem accepting_derivationTrace_suffix_nonterminalIncreaseCount_le_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    traceNonterminalIncreaseCount (trace.drop i) ≤ w.length := by
  have hnt :=
    accepting_derivationTrace_suffix_nonterminalCount_add_increase_eq_terminalIncreaseCount_of_isNormalForm
      (g := g) hNF htrace hlast hi
  have hterm :=
    accepting_derivationTrace_suffix_terminalIncreaseCount_le_target_length_of_isNormalForm
      (g := g) hNF htrace hlast hi
  omega

theorem accepting_derivationTrace_get_terminalCount_eq_terminalIncreaseCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialTerminalCount (trace.get ⟨i, hi⟩) =
      traceTerminalIncreaseCountUpTo i trace := by
  have hcount :=
    isDerivationTrace_get_terminalCount_eq_head_add_terminalIncreaseCountUpTo_of_isNormalForm
      hNF htrace hhead hi
  simpa using hcount

theorem accepting_derivationTrace_get_nonterminal_balanceUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialNonterminalCount (trace.get ⟨i, hi⟩) +
        traceNonterminalDecreaseCountUpTo i trace =
      1 + traceNonterminalIncreaseCountUpTo i trace := by
  have hbalance :=
    isDerivationTrace_get_nonterminal_balanceUpTo_of_isNormalForm
      hNF htrace hhead hi
  simpa using hbalance

theorem accepting_derivationTrace_get_length_eq_succ_nonterminalIncreaseCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    (trace.get ⟨i, hi⟩).length =
      traceNonterminalIncreaseCountUpTo i trace + 1 := by
  have hterm :=
    accepting_derivationTrace_get_terminalCount_eq_terminalIncreaseCountUpTo_of_isNormalForm
      hNF htrace hhead hi
  have hbalance :=
    accepting_derivationTrace_get_nonterminal_balanceUpTo_of_isNormalForm
      hNF htrace hhead hi
  have htd :=
    isDerivationTrace_terminalIncreaseCountUpTo_eq_nonterminalDecreaseCountUpTo_of_isNormalForm
      hNF htrace i
  have hlen :=
    sententialTerminalCount_add_nonterminalCount (trace.get ⟨i, hi⟩)
  omega

theorem isDerivationTrace_get_maxStackHeight_le_head_add_pushStepCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      sententialMaxStackHeight first + tracePushStepCountUpTo i trace := by
  induction i generalizing trace first with
  | zero =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          have hfirst : a = first := by simpa using hhead
          subst first
          simp
  | succ i ih =>
      cases trace with
      | nil =>
          simp at hi
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hi
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have hi_tail : i < (b :: rest).length := by simpa using hi
              have hget :
                  (a :: b :: rest).get ⟨i + 1, hi⟩ =
                    (b :: rest).get ⟨i, hi_tail⟩ := by
                simp
              have ih_tail :=
                ih (trace := b :: rest) (first := b) htrace.2 (by simp) hi_tail
              have hstep :=
                transforms_maxStackHeight_le_add_pushIndicator_of_isNormalForm
                  hNF htrace.1
              have hfirst : a = first := by simpa using hhead
              subst first
              rw [tracePushStepCountUpTo_succ_cons_cons, hget]
              by_cases hpush : TransformIsObservablePush a b
              · rw [if_pos hpush]
                have hstep' :
                    sententialMaxStackHeight b ≤ sententialMaxStackHeight a + 1 := by
                  simpa [hpush] using hstep
                omega
              · rw [if_neg hpush]
                have hstep' :
                    sententialMaxStackHeight b ≤ sententialMaxStackHeight a := by
                  simpa [hpush] using hstep
                omega

theorem accepting_derivationTrace_get_maxStackHeight_le_pushStepCountUpTo_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePushStepCountUpTo i trace := by
  have h :=
    isDerivationTrace_get_maxStackHeight_le_head_add_pushStepCountUpTo_of_isNormalForm
      hNF htrace hhead hi
  simpa using h

theorem isDerivationTrace_get_maxStackHeight_le_head_add_pushStepCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {first : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some first)
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      sententialMaxStackHeight first + tracePushStepCount trace := by
  have hprefix :=
    isDerivationTrace_get_maxStackHeight_le_head_add_pushStepCountUpTo_of_isNormalForm
      hNF htrace hhead hi
  have hle := tracePushStepCountUpTo_le_tracePushStepCount (g := g) i trace
  omega

theorem accepting_derivationTrace_get_maxStackHeight_le_pushStepCount_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePushStepCount trace := by
  have h :=
    isDerivationTrace_get_maxStackHeight_le_head_add_pushStepCount_of_isNormalForm
      hNF htrace hhead hi
  simpa using h

theorem accepting_derivationTrace_get_maxStackHeight_le_stackHeightDecrease_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      traceStackHeightDecrease trace := by
  have hheight :=
    accepting_derivationTrace_get_maxStackHeight_le_pushStepCount_of_isNormalForm
      hNF htrace hhead hi
  have hpush :=
    accepting_derivationTrace_pushStepCount_le_stackHeightDecrease
      (g := g) (trace := trace) (w := w) hhead hlast
  omega

theorem accepting_derivationTrace_get_maxStackHeight_le_pop_add_terminalErase_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤
      tracePopStepCount trace + traceTerminalEraseStackHeight trace := by
  have hheight :=
    accepting_derivationTrace_get_maxStackHeight_le_stackHeightDecrease_of_isNormalForm
      hNF htrace hhead hlast hi
  have hdec :=
    isDerivationTrace_stackHeightDecrease_eq_pop_add_terminalErase_of_isNormalForm
      hNF htrace
  omega

theorem accepting_derivationTrace_terminalIncreaseCountUpTo_le_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} (i : ℕ)
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceTerminalIncreaseCountUpTo i trace ≤ w.length := by
  have hle := traceTerminalIncreaseCountUpTo_le_traceTerminalIncreaseCount
    (g := g) i trace
  have htotal :=
    accepting_derivationTrace_terminalIncreaseCount_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast
  omega

theorem accepting_derivationTrace_nonterminalIncreaseCountUpTo_succ_le_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} (i : ℕ)
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceNonterminalIncreaseCountUpTo i trace + 1 ≤ w.length := by
  have hle := traceNonterminalIncreaseCountUpTo_le_traceNonterminalIncreaseCount
    (g := g) i trace
  have htotal :=
    accepting_derivationTrace_nonterminalIncreaseCount_succ_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast
  omega

theorem accepting_derivationTrace_nonterminalDecreaseCountUpTo_le_target_length_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} (i : ℕ)
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal)) :
    traceNonterminalDecreaseCountUpTo i trace ≤ w.length := by
  have hle := traceNonterminalDecreaseCountUpTo_le_traceNonterminalDecreaseCount
    (g := g) i trace
  have htotal_term :=
    accepting_derivationTrace_terminalIncreaseCount_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast
  have htotal_eq :=
    isDerivationTrace_terminalIncreaseCount_eq_nonterminalDecreaseCount_of_isNormalForm
      hNF htrace
  omega

theorem accepting_derivesIn_exists_derivationTrace_with_counts_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal)) :
    ∃ trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        traceTerminalIncreaseCount trace = w.length ∧
        traceNonterminalIncreaseCount trace + 1 = w.length := by
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn h
  exact ⟨trace, htrace, hlen, hhead, hlast,
    accepting_derivationTrace_terminalIncreaseCount_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast,
    accepting_derivationTrace_nonterminalIncreaseCount_succ_eq_target_length_of_isNormalForm
      hNF htrace hhead hlast⟩

theorem accepting_derivationTrace_get_length_le_target_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    (trace.get ⟨i, hi⟩).length ≤ w.length := by
  have hsuffix := isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
  have hlen :=
    derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix
  simpa using hlen

theorem accepting_derivationTrace_get_sententialStackHeight_le_of_isNormalForm_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    sententialStackHeight (trace.get ⟨i, hi⟩) ≤ w.length * B := by
  have htotal :=
    sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
      (g := g) (B := B) (w := trace.get ⟨i, hi⟩) (hstack i hi)
  have hnonterm :
      sententialNonterminalCount (trace.get ⟨i, hi⟩) ≤ w.length :=
    le_trans (sententialNonterminalCount_le_length _)
      (accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast hi)
  exact le_trans htotal (Nat.mul_le_mul_right B hnonterm)

theorem accepting_derivationTrace_get_encodeSentential_length_le_of_isNormalForm_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤ w.length * (B + 2) := by
  exact le_trans
    (encodeSentential_length_le_of_maxStackHeight_le (hstack i hi))
    (Nat.mul_le_mul_right (B + 2)
      (accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast hi))

theorem accepting_derivationTrace_get_encodeSentential_length_le_of_isNormalForm_stackBound_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    {i : ℕ} (hi : i < trace.length) :
    (encodeSentential (trace.get ⟨i, hi⟩)).length ≤ L * (B + 2) := by
  exact le_trans
    (accepting_derivationTrace_get_encodeSentential_length_le_of_isNormalForm_stackBound
      hNF htrace hlast hstack hi)
    (Nat.mul_le_mul_right (B + 2) hwlen)

theorem accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_stackBound_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B)
    (i : Fin (flatTrace trace).length) :
    (flatTrace trace).get i ∈ boundedFlatForms g (L * (B + 2)) := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [flatTrace_get trace hi]
  exact
    accepting_derivationTrace_get_encodeSentential_length_le_of_isNormalForm_stackBound_lengthBound
      hNF htrace hlast hwlen hstack hi

theorem accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_popBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P)
    (i : Fin (flatTrace trace).length) :
    (flatTrace trace).get i ∈ boundedFlatForms g (L + L + (P + L * B)) := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [flatTrace_get trace hi]
  exact
    accepting_derivationTrace_get_encodeSentential_length_le_popBudget_stackBound_lengthBound_of_isNormalForm
      hNF htrace hlast hwlen hbound hpop hi

theorem accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_stepBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B L n N : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hnN : n ≤ N)
    (i : Fin (flatTrace trace).length) :
    (flatTrace trace).get i ∈ boundedFlatForms g (L + L + (N + L * B)) := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [flatTrace_get trace hi]
  exact
    accepting_derivationTrace_get_encodeSentential_length_le_stepBudget_stackBound_lengthBound_of_isNormalForm
      hNF htrace hlen hlast hwlen hbound hnN hi

theorem accepting_derivationTrace_get_maxStackHeight_le_index_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ i := by
  have hprefix :=
    isDerivationTrace_derivesIn_from_head_get (g := g) htrace hhead hi
  have hheight := derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hprefix
  simpa using hheight

theorem accepting_derivationTrace_get_mem_boundedSententialForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    trace.get ⟨i, hi⟩ ∈ boundedSententialForms g w.length n := by
  refine ⟨?_, ?_⟩
  · exact accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi
  · have hheight :=
      accepting_derivationTrace_get_maxStackHeight_le_index_of_isNormalForm hNF htrace hhead hi
    have hi_le : i ≤ n := by omega
    exact le_trans hheight hi_le

theorem accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) ∈
      boundedSurfaceForms g w.length B := by
  apply surfaceOfTruncatedForm_mem_boundedSurfaceForms
  exact accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi

theorem accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (i : Fin (surfaceTrace B trace).length) :
    (surfaceTrace B trace).get i ∈ boundedSurfaceForms g w.length B := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [surfaceTrace_get B trace hi]
  exact accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm
    hNF htrace hlast hi

theorem accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    {i : ℕ} (hi : i < trace.length) :
    surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) ∈
      boundedSurfaceForms g L B := by
  apply surfaceOfTruncatedForm_mem_boundedSurfaceForms
  exact le_trans
    (accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi)
    hwlen

theorem accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm_lengthBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (i : Fin (surfaceTrace B trace).length) :
    (surfaceTrace B trace).get i ∈ boundedSurfaceForms g L B := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [surfaceTrace_get B trace hi]
  exact accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm_lengthBound
    hNF htrace hlast hwlen hi

theorem accepting_derivationTrace_get_surface_mem_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) ∈
      targetCompatibleBoundedSurfaceForms g w B := by
  apply surfaceOfTruncatedForm_mem_targetCompatibleBoundedSurfaceForms
  · exact accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi
  · have hsuffix :=
      isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
    have hsub := derivesIn_sententialTerminals_sublist (g := g) hsuffix
    simpa using hsub

theorem accepting_surfaceTrace_get_mem_targetCompatibleBoundedSurfaceForms
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (i : Fin (surfaceTrace B trace).length) :
    (surfaceTrace B trace).get i ∈ targetCompatibleBoundedSurfaceForms g w B := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [surfaceTrace_get B trace hi]
  exact accepting_derivationTrace_get_surface_mem_targetCompatibleBoundedSurfaceForms
    hNF htrace hlast hi

theorem accepting_derivationTrace_exists_surface_repeat_of_card_lt_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hwlen : w.length ≤ L)
    (hcard :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card <
        trace.length) :
    ∃ i j : Fin trace.length, i < j ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  have hcard' :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card <
        (surfaceTrace B trace).length := by
    simpa using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := surfaceTrace B trace)
      (boundedSurfaceForms g L B)
      (boundedSurfaceForms_finite g L B)
      (fun i =>
        accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm_lengthBound
          hNF htrace hlast hwlen i)
      hcard' with ⟨i, j, hij, hget⟩
  let i' : Fin trace.length := ⟨i.1, by simpa using i.2⟩
  let j' : Fin trace.length := ⟨j.1, by simpa using j.2⟩
  have hi : i.1 < trace.length := i'.2
  have hj : j.1 < trace.length := j'.2
  have hget' :
      (surfaceTrace B trace).get ⟨i.1, by simpa using hi⟩ =
        (surfaceTrace B trace).get ⟨j.1, by simpa using hj⟩ := by
    simpa using hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i.1, hi⟩) =
        surfaceOfTruncatedForm B (trace.get ⟨j.1, hj⟩) := by
    rw [surfaceTrace_get B trace hi] at hget'
    rw [surfaceTrace_get B trace hj] at hget'
    exact hget'
  refine ⟨i', j', ?_, ?_⟩
  · exact hij
  · exact hsurface

theorem accepting_derivationTrace_exists_surface_repeat_of_card_lt_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hcard :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card <
        trace.length) :
    ∃ i j : Fin trace.length, i < j ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  have hcard' :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card <
        (surfaceTrace B trace).length := by
    simpa using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := surfaceTrace B trace)
      (boundedSurfaceForms g w.length B)
      (boundedSurfaceForms_finite g w.length B)
      (fun i =>
        accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm
          hNF htrace hlast i)
      hcard' with ⟨i, j, hij, hget⟩
  let i' : Fin trace.length := ⟨i.1, by simpa using i.2⟩
  let j' : Fin trace.length := ⟨j.1, by simpa using j.2⟩
  have hi : i.1 < trace.length := i'.2
  have hj : j.1 < trace.length := j'.2
  have hget' :
      (surfaceTrace B trace).get ⟨i.1, by simpa using hi⟩ =
        (surfaceTrace B trace).get ⟨j.1, by simpa using hj⟩ := by
    simpa using hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i.1, hi⟩) =
        surfaceOfTruncatedForm B (trace.get ⟨j.1, hj⟩) := by
    rw [surfaceTrace_get B trace hi] at hget'
    rw [surfaceTrace_get B trace hj] at hget'
    exact hget'
  refine ⟨i', j', ?_, ?_⟩
  · exact hij
  · exact hsurface

theorem accepting_derivationTrace_exists_targetCompatible_surface_repeat_of_card_lt_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        trace.length) :
    ∃ i j : Fin trace.length, i < j ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  have hcard' :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        (surfaceTrace B trace).length := by
    simpa using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := surfaceTrace B trace)
      (targetCompatibleBoundedSurfaceForms g w B)
      (targetCompatibleBoundedSurfaceForms_finite g w B)
      (fun i =>
        accepting_surfaceTrace_get_mem_targetCompatibleBoundedSurfaceForms
          hNF htrace hlast i)
      hcard' with ⟨i, j, hij, hget⟩
  let i' : Fin trace.length := ⟨i.1, by simpa using i.2⟩
  let j' : Fin trace.length := ⟨j.1, by simpa using j.2⟩
  have hi : i.1 < trace.length := i'.2
  have hj : j.1 < trace.length := j'.2
  have hget' :
      (surfaceTrace B trace).get ⟨i.1, by simpa using hi⟩ =
        (surfaceTrace B trace).get ⟨j.1, by simpa using hj⟩ := by
    simpa using hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i.1, hi⟩) =
        surfaceOfTruncatedForm B (trace.get ⟨j.1, hj⟩) := by
    rw [surfaceTrace_get B trace hi] at hget'
    rw [surfaceTrace_get B trace hj] at hget'
    exact hget'
  refine ⟨i', j', ?_, ?_⟩
  · exact hij
  · exact hsurface

/-- Prefix-local target-compatible surface pigeonhole. If the first `m + 1` entries of an
accepting surface trace are longer than the finite target-compatible surface set, then two
surfaces already repeat inside that prefix. -/
theorem accepting_derivationTrace_exists_targetCompatible_surface_repeat_before_of_card_lt
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B m : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        m + 1) :
    ∃ i j : Fin trace.length, i < j ∧ j.1 ≤ m ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  let xs := (surfaceTrace B trace).take (m + 1)
  have htakeLen : xs.length = m + 1 := by
    simp [xs, List.length_take, surfaceTrace_length, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
  have hmem :
      ∀ i : Fin xs.length,
        xs.get i ∈ targetCompatibleBoundedSurfaceForms g w B := by
    intro i
    have hiPrefix : i.1 < m + 1 := by
      simpa [htakeLen] using i.2
    have hiSurface : i.1 < (surfaceTrace B trace).length := by
      rw [surfaceTrace_length]
      omega
    have hget :
        xs.get i =
          (surfaceTrace B trace).get ⟨i.1, hiSurface⟩ := by
      change xs[i.1] = (surfaceTrace B trace)[i.1]
      simp [xs]
    have hfull :=
      accepting_surfaceTrace_get_mem_targetCompatibleBoundedSurfaceForms
        (g := g) hNF htrace hlast ⟨i.1, hiSurface⟩
    rw [hget]
    exact hfull
  have hcard' :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        xs.length := by
    simpa [htakeLen] using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := xs)
      (targetCompatibleBoundedSurfaceForms g w B)
      (targetCompatibleBoundedSurfaceForms_finite g w B)
      hmem hcard' with ⟨i, j, hij, hget⟩
  have hiPrefix : i.1 < m + 1 := by
    simpa [htakeLen] using i.2
  have hjPrefix : j.1 < m + 1 := by
    simpa [htakeLen] using j.2
  have hiTrace : i.1 < trace.length := by omega
  have hjTrace : j.1 < trace.length := by omega
  let i' : Fin trace.length := ⟨i.1, hiTrace⟩
  let j' : Fin trace.length := ⟨j.1, hjTrace⟩
  have hiSurface : i.1 < (surfaceTrace B trace).length := by
    simpa [surfaceTrace_length] using hiTrace
  have hjSurface : j.1 < (surfaceTrace B trace).length := by
    simpa [surfaceTrace_length] using hjTrace
  have hget_i :
      xs.get i = (surfaceTrace B trace).get ⟨i.1, hiSurface⟩ := by
    change xs[i.1] = (surfaceTrace B trace)[i.1]
    simp [xs]
  have hget_j :
      xs.get j = (surfaceTrace B trace).get ⟨j.1, hjSurface⟩ := by
    change xs[j.1] = (surfaceTrace B trace)[j.1]
    simp [xs]
  have hsurfaceTrace :
      (surfaceTrace B trace).get ⟨i.1, hiSurface⟩ =
        (surfaceTrace B trace).get ⟨j.1, hjSurface⟩ := by
    rw [← hget_i, ← hget_j]
    exact hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get i') =
        surfaceOfTruncatedForm B (trace.get j') := by
    rw [surfaceTrace_get B trace hiTrace] at hsurfaceTrace
    rw [surfaceTrace_get B trace hjTrace] at hsurfaceTrace
    exact hsurfaceTrace
  refine ⟨i', j', ?_, ?_, hsurface⟩
  · exact hij
  ·
    change j.1 ≤ m
    exact Nat.lt_succ_iff.mp hjPrefix

/-- Interval-local target-compatible surface pigeonhole. If an interval `[a, m]` of an
accepting surface trace is longer than the finite target-compatible surface set, then two
surfaces repeat inside that interval. -/
theorem accepting_derivationTrace_exists_targetCompatible_surface_repeat_between_of_card_lt
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B a m : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (ham : a ≤ m)
    (hm : m < trace.length)
    (hcard :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        m + 1 - a) :
    ∃ i j : Fin trace.length, i < j ∧ a ≤ i.1 ∧ j.1 ≤ m ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  let xs := ((surfaceTrace B trace).drop a).take (m + 1 - a)
  have htakeLen : xs.length = m + 1 - a := by
    have hlen_le : m + 1 - a ≤ (surfaceTrace B trace).length - a := by
      rw [surfaceTrace_length]
      omega
    dsimp [xs]
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left hlen_le
  have hmem :
      ∀ i : Fin xs.length,
        xs.get i ∈ targetCompatibleBoundedSurfaceForms g w B := by
    intro i
    have hiInterval : i.1 < m + 1 - a := by
      simpa [htakeLen] using i.2
    have hiTrace : a + i.1 < trace.length := by
      omega
    have hiSurface : a + i.1 < (surfaceTrace B trace).length := by
      simpa [surfaceTrace_length] using hiTrace
    have hget :
        xs.get i =
          (surfaceTrace B trace).get ⟨a + i.1, hiSurface⟩ := by
      change xs[i.1] = (surfaceTrace B trace)[a + i.1]
      simp [xs]
    have hfull :=
      accepting_surfaceTrace_get_mem_targetCompatibleBoundedSurfaceForms
        (g := g) hNF htrace hlast ⟨a + i.1, hiSurface⟩
    rw [hget]
    exact hfull
  have hcard' :
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card <
        xs.length := by
    simpa [htakeLen] using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := xs)
      (targetCompatibleBoundedSurfaceForms g w B)
      (targetCompatibleBoundedSurfaceForms_finite g w B)
      hmem hcard' with ⟨i, j, hij, hget⟩
  have hiInterval : i.1 < m + 1 - a := by
    simpa [htakeLen] using i.2
  have hjInterval : j.1 < m + 1 - a := by
    simpa [htakeLen] using j.2
  have hiTrace : a + i.1 < trace.length := by omega
  have hjTrace : a + j.1 < trace.length := by omega
  let i' : Fin trace.length := ⟨a + i.1, hiTrace⟩
  let j' : Fin trace.length := ⟨a + j.1, hjTrace⟩
  have hiSurface : a + i.1 < (surfaceTrace B trace).length := by
    simpa [surfaceTrace_length] using hiTrace
  have hjSurface : a + j.1 < (surfaceTrace B trace).length := by
    simpa [surfaceTrace_length] using hjTrace
  have hget_i :
      xs.get i = (surfaceTrace B trace).get ⟨a + i.1, hiSurface⟩ := by
    change xs[i.1] = (surfaceTrace B trace)[a + i.1]
    simp [xs]
  have hget_j :
      xs.get j = (surfaceTrace B trace).get ⟨a + j.1, hjSurface⟩ := by
    change xs[j.1] = (surfaceTrace B trace)[a + j.1]
    simp [xs]
  have hsurfaceTrace :
      (surfaceTrace B trace).get ⟨a + i.1, hiSurface⟩ =
        (surfaceTrace B trace).get ⟨a + j.1, hjSurface⟩ := by
    rw [← hget_i, ← hget_j]
    exact hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get i') =
        surfaceOfTruncatedForm B (trace.get j') := by
    rw [surfaceTrace_get B trace hiTrace] at hsurfaceTrace
    rw [surfaceTrace_get B trace hjTrace] at hsurfaceTrace
    exact hsurfaceTrace
  refine ⟨i', j', ?_, ?_, ?_, hsurface⟩
  · change a + i.1 < a + j.1
    omega
  · change a ≤ a + i.1
    omega
  · change a + j.1 ≤ m
    omega

theorem accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  exact List.Nodup.length_le_finite_set_card_of_get_mem hnodup
    (boundedSententialForms g w.length B)
    (boundedSententialForms_finite g w.length B)
    (fun i => ⟨accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast i.2,
      hstack i.1 i.2⟩)

theorem minimal_accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  exact accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    hNF htrace hlast hnodup hstack

theorem accepting_flatTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    (flatTrace trace).length ≤
      (Set.Finite.toFinset (boundedFlatForms_finite g (L * (B + 2)))).card := by
  have hflatNodup : (flatTrace trace).Nodup := by
    simpa [flatTrace] using hnodup.map encodeSentential_injective
  exact List.Nodup.length_le_finite_set_card_of_get_mem hflatNodup
    (boundedFlatForms g (L * (B + 2)))
    (boundedFlatForms_finite g (L * (B + 2)))
    (accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_stackBound_lengthBound
      hNF htrace hlast hwlen hstack)

theorem accepting_derivationTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedFlatForms_finite g (L * (B + 2)))).card := by
  simpa [flatTrace_length] using
    accepting_flatTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
      hNF htrace hlast hnodup hwlen hstack

theorem minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedFlatForms_finite g (L * (B + 2)))).card := by
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  exact accepting_derivationTrace_length_le_boundedFlatForms_card_of_stackBound_lengthBound
    hNF htrace hlast hnodup hwlen hstack

theorem accepting_flatTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P) :
    (flatTrace trace).length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (P + L * B)))).card := by
  have hflatNodup : (flatTrace trace).Nodup := by
    simpa [flatTrace] using hnodup.map encodeSentential_injective
  exact List.Nodup.length_le_finite_set_card_of_get_mem hflatNodup
    (boundedFlatForms g (L + L + (P + L * B)))
    (boundedFlatForms_finite g (L + L + (P + L * B)))
    (accepting_flatTrace_get_mem_boundedFlatForms_of_isNormalForm_popBudget_stackBound_lengthBound
      hNF htrace hlast hwlen hbound hpop)

theorem accepting_derivationTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {L B P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (P + L * B)))).card := by
  simpa [flatTrace_length] using
    accepting_flatTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
      hNF htrace hlast hnodup hwlen hbound hpop

theorem minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B P : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hpop : tracePopStepCount trace ≤ P) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (P + L * B)))).card := by
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  exact accepting_derivationTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
    hNF htrace hlast hnodup hwlen hbound hpop

theorem accepting_flatTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B N : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hnN : n ≤ N) :
    (flatTrace trace).length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (N + L * B)))).card := by
  have hpop : tracePopStepCount trace ≤ N :=
    le_trans (tracePopStepCount_le_steps_of_length_eq (g := g) hlen) hnN
  exact
    accepting_flatTrace_length_le_boundedFlatForms_card_of_popBudget_stackBound_lengthBound
      (g := g) (L := L) (B := B) (P := N)
      hNF htrace hlast hnodup hwlen hbound hpop

theorem accepting_derivationTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B N : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hnN : n ≤ N) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (N + L * B)))).card := by
  simpa [flatTrace_length] using
    accepting_flatTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
      hNF htrace hlen hlast hnodup hwlen hbound hnN

theorem minimal_accepting_derivationTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B N : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    (hbound : ∀ x ∈ trace, sententialMaxStackHeight x ≤ B)
    (hnN : n ≤ N) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedFlatForms_finite g (L + L + (N + L * B)))).card := by
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  exact accepting_derivationTrace_length_le_boundedFlatForms_card_of_stepBudget_stackBound_lengthBound
    hNF htrace hlen hlast hnodup hwlen hbound hnN

/-- Length-uniform version of the bounded-surface pigeonhole bound. If the accepted word has
length at most `L`, then a shortest stack-bounded accepting trace is bounded by the finite
surface space with length parameter `L`, independent of the particular target word. -/
theorem minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {L B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card := by
  apply le_of_not_gt
  intro hcard
  obtain ⟨i, j, hij, hsurface⟩ :=
    accepting_derivationTrace_exists_surface_repeat_of_card_lt_lengthBound
      hNF htrace hlast hwlen hcard
  have hactual : trace.get i = trace.get j := by
    have hi_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get i)) = trace.get i :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack i.1 i.2)
    have hj_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get j)) = trace.get j :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack j.1 j.2)
    have herase := congrArg eraseSurfaceForm hsurface
    rwa [hi_eq, hj_eq] at herase
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  have hij_eq : i = j := (List.Nodup.get_inj_iff hnodup).mp hactual
  exact (ne_of_lt hij) hij_eq

/-- A shortest accepting derivation whose stacks are bounded by `B` has no more steps than
there are bounded visible-stack surface forms of target length `|w|`.

This is the same pigeonhole argument as the full sentential-form bound, but expressed on the
finite surface alphabet. A repeated bounded surface would erase back to a repeated actual
sentential form because all actual stacks are already below `B`, contradicting minimality. -/
theorem minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card := by
  apply le_of_not_gt
  intro hcard
  obtain ⟨i, j, hij, hsurface⟩ :=
    accepting_derivationTrace_exists_surface_repeat_of_card_lt_length
      hNF htrace hlast hcard
  have hactual : trace.get i = trace.get j := by
    have hi_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get i)) = trace.get i :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack i.1 i.2)
    have hj_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get j)) = trace.get j :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack j.1 j.2)
    have herase := congrArg eraseSurfaceForm hsurface
    rwa [hi_eq, hj_eq] at herase
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  have hij_eq : i = j := (List.Nodup.get_inj_iff hnodup).mp hactual
  exact (ne_of_lt hij) hij_eq

/-- Target-compatible version of the bounded-surface pigeonhole bound. The finite set includes
only surfaces whose visible terminal yield is a sublist of the accepted word. -/
theorem minimal_accepting_derivationTrace_length_le_targetCompatibleBoundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card := by
  apply le_of_not_gt
  intro hcard
  obtain ⟨i, j, hij, hsurface⟩ :=
    accepting_derivationTrace_exists_targetCompatible_surface_repeat_of_card_lt_length
      hNF htrace hlast hcard
  have hactual : trace.get i = trace.get j := by
    have hi_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get i)) = trace.get i :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack i.1 i.2)
    have hj_eq :
        eraseSurfaceForm (surfaceOfTruncatedForm B (trace.get j)) = trace.get j :=
      eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
        (hstack j.1 j.2)
    have herase := congrArg eraseSurfaceForm hsurface
    rwa [hi_eq, hj_eq] at herase
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  have hij_eq : i = j := (List.Nodup.get_inj_iff hnodup).mp hactual
  exact (ne_of_lt hij) hij_eq

theorem accepting_derivationTrace_length_le_boundedSententialForms_card_of_pushCount
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedSententialForms_finite g w.length (tracePushStepCount trace))).card := by
  apply accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    hNF htrace hlast hnodup
  intro i hi
  exact accepting_derivationTrace_get_maxStackHeight_le_pushStepCount_of_isNormalForm
    hNF htrace hhead hi

theorem minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_pushCount
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) :
    trace.length ≤
      (Set.Finite.toFinset
        (boundedSurfaceForms_finite g w.length (tracePushStepCount trace))).card := by
  apply minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound
    hNF htrace hlen hhead hlast hmin
  intro i hi
  exact accepting_derivationTrace_get_maxStackHeight_le_pushStepCount_of_isNormalForm
    hNF htrace hhead hi

theorem minimal_accepting_derivationTrace_length_le_targetCompatibleBoundedSurfaceForms_card_of_pushCount
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) :
    trace.length ≤
      (Set.Finite.toFinset
        (targetCompatibleBoundedSurfaceForms_finite g w (tracePushStepCount trace))).card := by
  apply minimal_accepting_derivationTrace_length_le_targetCompatibleBoundedSurfaceForms_card_of_stackBound
    hNF htrace hlen hhead hlast hmin
  intro i hi
  exact accepting_derivationTrace_get_maxStackHeight_le_pushStepCount_of_isNormalForm
    hNF htrace hhead hi

theorem exists_minimal_accepting_derivationTrace_with_targetCompatibleSurface_bound_of_pushCount
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T}
    (hgen : g.Generates w) :
    ∃ n trace,
      IsDerivationTrace g trace ∧
        trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
        (∀ m,
          g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
        n <
          (Set.Finite.toFinset
            (targetCompatibleBoundedSurfaceForms_finite g w (tracePushStepCount trace))).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  have hbound :=
    minimal_accepting_derivationTrace_length_le_targetCompatibleBoundedSurfaceForms_card_of_pushCount
      hNF htrace hlen hhead hlast hmin
  refine ⟨n, trace, htrace, hlen, hhead, hlast, hder, hmin, ?_⟩
  omega

/-- Counted-derivation version of
`minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound`. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card := by
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn h
  have hbound :=
    minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound
      (B := B) hNF htrace hlen hhead hlast hmin ?_
  · simpa [hlen] using hbound
  · intro i hi
    have hi_le : i ≤ n := by omega
    exact hstack i (trace.get ⟨i, hi⟩)
      (isDerivationTrace_get_intermediate htrace hlen hhead hlast hi_le)

/-- A shortest accepting derivation with stacks bounded by `B` uses strictly fewer steps than
the finite bounded-surface search space. -/
theorem minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n < (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card := by
  have hsucc :=
    minimal_accepting_derivesIn_steps_succ_le_boundedSurfaceForms_card_of_stackBound
      hNF h hmin hstack
  omega

/-- Counted-derivation version of the target-compatible bounded-surface trace bound. -/
theorem minimal_accepting_derivesIn_steps_succ_le_targetCompatibleBoundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n + 1 ≤
      (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card := by
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn h
  have hbound :=
    minimal_accepting_derivationTrace_length_le_targetCompatibleBoundedSurfaceForms_card_of_stackBound
      (B := B) hNF htrace hlen hhead hlast hmin ?_
  · simpa [hlen] using hbound
  · intro i hi
    have hi_le : i ≤ n := by omega
    exact hstack i (trace.get ⟨i, hi⟩)
      (isDerivationTrace_get_intermediate htrace hlen hhead hlast hi_le)

/-- A shortest accepting derivation with stacks bounded by `B` uses fewer steps than the
target-compatible finite bounded-surface search space. -/
theorem minimal_accepting_derivesIn_steps_lt_targetCompatibleBoundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n < (Set.Finite.toFinset (targetCompatibleBoundedSurfaceForms_finite g w B)).card := by
  have hsucc :=
    minimal_accepting_derivesIn_steps_succ_le_targetCompatibleBoundedSurfaceForms_card_of_stackBound
      hNF h hmin hstack
  omega

/-- Counted-derivation version of the length-uniform bounded-surface trace bound. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSurfaceForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T} {L : ℕ}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card := by
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn h
  have hbound :=
    minimal_accepting_derivationTrace_length_le_boundedSurfaceForms_card_of_stackBound_lengthBound
      (B := B) hNF htrace hlen hhead hlast hmin hwlen ?_
  · simpa [hlen] using hbound
  · intro i hi
    have hi_le : i ≤ n := by omega
    exact hstack i (trace.get ⟨i, hi⟩)
      (isDerivationTrace_get_intermediate htrace hlen hhead hlast hi_le)

/-- A shortest accepting derivation with stacks bounded by `B` uses strictly fewer steps than
the finite bounded-surface search space for any length bound `L` on the target word. -/
theorem minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T} {L : ℕ}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hwlen : w.length ≤ L)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card := by
  have hsucc :=
    minimal_accepting_derivesIn_steps_succ_le_boundedSurfaceForms_card_of_stackBound_lengthBound
      hNF h hmin hwlen hstack
  omega

/-- Generated-word version of the length-uniform bounded-surface finite-search witness. -/
theorem exists_minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound_lengthBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T} {L B : ℕ}
    (hgen : g.Generates w)
    (hwlen : w.length ≤ L)
    (hstack : ∀ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) →
      (∀ m, g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) →
      ∀ i x,
        DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
          sententialMaxStackHeight x ≤ B) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      n < (Set.Finite.toFinset (boundedSurfaceForms_finite g L B)).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  exact ⟨n, hder, hmin,
    minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound_lengthBound
      hNF hder hmin hwlen (hstack n hder hmin)⟩

/-- Generated-word version of the bounded-surface finite-search witness. Once a stack bound is
known for the chosen shortest accepting derivation, the accepting derivation can be searched for
below the finite bounded-surface cardinal. -/
theorem exists_minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T} {B : ℕ}
    (hgen : g.Generates w)
    (hstack : ∀ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) →
      (∀ m, g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) →
      ∀ i x,
        DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
          sententialMaxStackHeight x ≤ B) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      n < (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  exact ⟨n, hder, hmin,
    minimal_accepting_derivesIn_steps_lt_boundedSurfaceForms_card_of_stackBound
      hNF hder hmin (hstack n hder hmin)⟩

/-- Generated-word version of the target-compatible bounded-surface finite-search witness. -/
theorem exists_minimal_accepting_derivesIn_steps_lt_targetCompatibleBoundedSurfaceForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T} {B : ℕ}
    (hgen : g.Generates w)
    (hstack : ∀ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) →
      (∀ m, g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) →
      ∀ i x,
        DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
          sententialMaxStackHeight x ≤ B) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      n < (Set.Finite.toFinset
        (targetCompatibleBoundedSurfaceForms_finite g w B)).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  exact ⟨n, hder, hmin,
    minimal_accepting_derivesIn_steps_lt_targetCompatibleBoundedSurfaceForms_card_of_stackBound
      hNF hder hmin (hstack n hder hmin)⟩

theorem accepting_derivesInIntermediate_length_le_target_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    x.length ≤ w.length := by
  have hlen :=
    derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hmid.2.2
  simpa using hlen

theorem accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    sententialMaxStackHeight x ≤ i := by
  have hheight := derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hmid.2.1
  simpa using hheight

theorem accepting_derivesInIntermediate_mem_boundedSententialForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    x ∈ boundedSententialForms g w.length n := by
  exact ⟨accepting_derivesInIntermediate_length_le_target_of_isNormalForm hNF hmid,
    le_trans (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)
      hmid.1⟩

theorem accepting_derivesInIntermediate_sententialTerminals_sublist_target
    {g : IndexedGrammar T} {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    (sententialTerminals x).Sublist w := by
  have hsub := derivesIn_sententialTerminals_sublist (g := g) hmid.2.2
  simpa using hsub

theorem accepting_derivesInIntermediate_terminalCount_le_target
    {g : IndexedGrammar T} {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    sententialTerminalCount x ≤ w.length := by
  have hsub := accepting_derivesInIntermediate_sententialTerminals_sublist_target
    (g := g) hmid
  simpa using hsub.length_le

theorem accepting_derivesInIntermediate_sententialStackHeight_le_of_isNormalForm_stackBound
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i B : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x)
    (hstack : sententialMaxStackHeight x ≤ B) :
    sententialStackHeight x ≤ w.length * B := by
  have htotal :=
    sententialStackHeight_le_nonterminalCount_mul_of_maxStackHeight_le
      (g := g) (B := B) (w := x) hstack
  have hnonterm : sententialNonterminalCount x ≤ w.length :=
    le_trans (sententialNonterminalCount_le_length x)
      (accepting_derivesInIntermediate_length_le_target_of_isNormalForm hNF hmid)
  exact le_trans htotal (Nat.mul_le_mul_right B hnonterm)

theorem accepting_derivesInIntermediate_sententialStackHeight_le_target_mul_index_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    sententialStackHeight x ≤ w.length * i :=
  accepting_derivesInIntermediate_sententialStackHeight_le_of_isNormalForm_stackBound
    hNF hmid
    (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)

/-- If a shortest accepting derivation has all intermediate stack heights bounded by `B`, then
its step count is bounded by the finite set of sentential forms with length at most the target
word and stack height at most `B`. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  refine minimal_derivesIn_steps_succ_le_card_of_intermediates_mem h hmin
    (boundedSententialForms g w.length B)
    (boundedSententialForms_finite g w.length B) ?_
  intro i x hmid
  exact ⟨accepting_derivesInIntermediate_length_le_target_of_isNormalForm hNF hmid,
    hstack i x hmid⟩

/-- The previous cardinal bound instantiated with the elementary per-step stack-height bound. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length n)).card := by
  apply minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card_of_stackBound
    hNF h hmin
  intro i x hmid
  exact le_trans
    (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)
    hmid.1

/-- Every generated word has a shortest accepting derivation whose step count is squeezed
between the word length and the finite set of elementary bounded sentential forms. -/
theorem exists_minimal_accepting_derivesIn_with_boundedSententialForms_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T}
    (hgen : g.Generates w) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      w.length ≤ n ∧
      n + 1 ≤
        (Set.Finite.toFinset (boundedSententialForms_finite g w.length n)).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  exact ⟨n, hder, hmin, generated_length_le_derivesIn_steps_of_isNormalForm hNF hder,
    minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card hNF hder hmin⟩

theorem intermediate_sententialTerminals_sublist_target {g : IndexedGrammar T}
    {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    (sententialTerminals x).Sublist w := by
  have hsub := derives_sententialTerminals_sublist (g := g) hsuffix
  simpa using hsub

theorem intermediate_terminalCount_le_target {g : IndexedGrammar T}
    {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    sententialTerminalCount x ≤ w.length := by
  have hsub := intermediate_sententialTerminals_sublist_target (g := g) hsuffix
  simpa using hsub.length_le

/-- In an accepting derivation of a no-ε grammar, every intermediate sentential form on the
chosen suffix has length at most the target word. -/
theorem intermediate_length_le_target_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    x.length ≤ w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hsuffix
  simpa using hlen

/-- Every sentential form reachable from the start of a no-ε grammar is nonempty. -/
theorem reachable_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym}
    (hprefix : g.Derives [ISym.indexed g.initial []] x) :
    0 < x.length := by
  have hlen := derives_length_le_of_noEpsilon hne hprefix
  simp at hlen
  omega

/-- In an accepting derivation of a no-ε grammar, every intermediate sentential form is
nonempty and has length at most the target word. -/
theorem accepting_intermediate_length_bounds_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hprefix : g.Derives [ISym.indexed g.initial []] x)
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    0 < x.length ∧ x.length ≤ w.length :=
  ⟨reachable_length_pos_of_noEpsilon hne hprefix,
    intermediate_length_le_target_of_noEpsilon hne hsuffix⟩

/-- In an accepting derivation of a no-ε grammar, the number of live nonterminals in any
intermediate sentential form is bounded by the target word length. -/
theorem intermediate_nonterminalCount_le_target_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    sententialNonterminalCount x ≤ w.length :=
  le_trans (sententialNonterminalCount_le_length x)
    (intermediate_length_le_target_of_noEpsilon hne hsuffix)

/-- In an accepting derivation of a normal-form grammar, every intermediate sentential form on
the chosen suffix has length at most the target word. -/
theorem intermediate_length_le_target_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    x.length ≤ w.length :=
  intermediate_length_le_target_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix

/-- In an accepting derivation of a normal-form grammar, every intermediate sentential form is
nonempty and has length at most the target word. -/
theorem accepting_intermediate_length_bounds_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hprefix : g.Derives [ISym.indexed g.initial []] x)
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    0 < x.length ∧ x.length ≤ w.length :=
  accepting_intermediate_length_bounds_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF)
    hprefix hsuffix

/-- In an accepting derivation of a normal-form grammar, the number of live nonterminals in
any intermediate sentential form is bounded by the target word length. -/
theorem intermediate_nonterminalCount_le_target_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    sententialNonterminalCount x ≤ w.length :=
  intermediate_nonterminalCount_le_target_of_noEpsilon
    (g.noEpsilon_of_isNormalForm hNF) hsuffix

/-- A no-ε indexed grammar can only generate nonempty words. -/
theorem generated_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {w : List T} (hgen : g.Generates w) :
    0 < w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hgen
  simpa using hlen

/-- A normal-form indexed grammar can only generate nonempty words. -/
theorem generated_length_pos_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T} (hgen : g.Generates w) :
    0 < w.length :=
  generated_length_pos_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hgen

end IndexedGrammar
