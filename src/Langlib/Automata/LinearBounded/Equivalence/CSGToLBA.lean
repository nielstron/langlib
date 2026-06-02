module

public import Langlib.Automata.LinearBounded.Definition
public import Langlib.Grammars.Unrestricted.Definition
public import Langlib.Grammars.NonContracting.Definition
import Mathlib.Tactic
@[expose]
public section



/-!
# Context-Sensitive Grammar → LBA (Kuroda's Construction)

This file builds a nondeterministic linearly bounded automaton from a non-contracting
grammar with finitely many nonterminals, establishing the genuine content of the
direction CS → LBA.

Given a non-contracting grammar `g₀` (every rule's output is at least as long as its
input pattern) with `Finite g₀.nt`, on input `w` of length `n` the automaton works on a
tape of exactly `n` cells whose alphabet packs two "tracks":

* **track 1** — the frozen input symbols (so the final comparison `track2 = w` is possible);
* **track 2** — a *working sentential form* over the finite grammar-symbol alphabet,
  initialised to `S` (the start symbol) followed by blanks.

The automaton nondeterministically applies grammar rules to track 2 (rewriting the matched
pattern in place, shifting the suffix right into the trailing blanks when the rule grows the
form) and accepts when track 2 spells exactly the input word. Non-contraction guarantees that
every sentential form of a derivation of `w` has length `≤ n`, so the bounded tape suffices.

## References

* Kuroda, S.-Y. (1964), "Classes of languages and linear-bounded automata".
* Hopcroft, Motwani, Ullman, *Introduction to Automata Theory, Languages, and Computation*,
  Chapter 9.
-/

namespace KurodaConstruction

open List Relation Classical

noncomputable section

variable {T : Type}

/-- `symbol T N` is in bijection with the sum `T ⊕ N` (terminal ↦ left, nonterminal ↦ right).
Used to transport `Fintype` onto the grammar-symbol work alphabet. -/
def symbolEquivSum (T N : Type) : symbol T N ≃ T ⊕ N where
  toFun := fun s => match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n
  invFun := fun s => match s with
    | Sum.inl t => .terminal t
    | Sum.inr n => .nonterminal n
  left_inv := fun s => by cases s <;> rfl
  right_inv := fun s => by cases s <;> rfl

/-- The grammar-symbol alphabet is finite whenever both the terminal and nonterminal alphabets
are. -/
instance instFintypeSymbol (T N : Type) [Fintype T] [Fintype N] : Fintype (symbol T N) :=
  Fintype.ofEquiv (T ⊕ N) (symbolEquivSum T N).symm

/-! ### The simulating machine

We build a backward (reductive) simulator. On input `w` the tape starts with the `|w|`
input cells `some (Sum.inl wᵢ)`; the machine first converts them to *work cells*
`some (Sum.inr (isLeftEnd, isRightEnd, workSym))`, where each `workSym` is a grammar symbol
(initially the terminal `wᵢ`) or the blank `#` (`none`). The boundary bits are set during the
conversion sweep: cell `0` is the start (the head begins there), and the right end is detected
the moment the rightward sweep re-reads an already-converted cell (the clamp at the last cell).

It then nondeterministically replays a derivation **in reverse**: each grammar rule
`input_L ++ [N] ++ input_R → output_string` is applied as `output_string ↦ input_L ++ [N] ++
input_R`, padding the freed cells with `#`. Symbols are kept contiguous by *bubbling* blanks
past symbols (a length-preserving swap of adjacent work cells). The machine accepts when the
non-blank work symbols spell exactly `[S]` (the start symbol), verified by a sweep between the
boundary markers. -/
section Machine

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- A bound on rule lengths: at least every rule's output length. -/
def ruleBound : ℕ := (g₀.rules.map (fun r => r.output_string.length)).foldr max 0

/-- The work symbol stored in a cell: a grammar symbol, or the blank `#` (`none`). -/
abbrev KWork := Option (symbol T g₀.nt)

/-- The work-cell alphabet `Γ`: `(isLeftEnd, isRightEnd, workSymbol)`. -/
abbrev KGamma := Bool × Bool × KWork g₀

/-- Control states of the backward simulator. -/
inductive KState where
  /-- Convert cell `0` (the known left end): mark `isLeftEnd`, keep the terminal. -/
  | init0
  /-- Convert subsequent cells left-to-right; detect the right end on a clamp. -/
  | initSweep
  /-- Roaming simulation state: move freely, or start applying a rule / the accept check. -/
  | sim
  /-- Applying the `r`-th rule backward in a single left-to-right pass: skip blanks, match the
  `k`-th symbol of `output_string`, writing the replacement (`patList[k]` if `k < |patList|`,
  else blank) into that cell in place. -/
  | applyRule (r : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1))
  /-- Go to the left end (marked) to begin the accept check. -/
  | gotoLeft
  /-- Accept-check sweep; `seen` records whether the unique start symbol was passed. -/
  | check (seen : Bool)
  /-- The (unique) accepting state. -/
  | accept
  deriving DecidableEq

instance : Fintype (KState g₀) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ Unit ⊕ Unit ⊕ (Fin g₀.rules.length × Fin (ruleBound g₀ + 1)) ⊕
      Unit ⊕ Bool ⊕ Unit)
    { toFun := fun x => match x with
        | .inl _ => .init0
        | .inr (.inl _) => .initSweep
        | .inr (.inr (.inl _)) => .sim
        | .inr (.inr (.inr (.inl (r, k)))) => .applyRule r k
        | .inr (.inr (.inr (.inr (.inl _)))) => .gotoLeft
        | .inr (.inr (.inr (.inr (.inr (.inl b))))) => .check b
        | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .accept
      invFun := fun x => match x with
        | .init0 => .inl ()
        | .initSweep => .inr (.inl ())
        | .sim => .inr (.inr (.inl ()))
        | .applyRule r k => .inr (.inr (.inr (.inl (r, k))))
        | .gotoLeft => .inr (.inr (.inr (.inr (.inl ()))))
        | .check b => .inr (.inr (.inr (.inr (.inr (.inl b)))))
        | .accept => .inr (.inr (.inr (.inr (.inr (.inr ())))))
      left_inv := fun x => by
        rcases x with _|_|_|⟨_,_⟩|_|_|_ <;> rfl
      right_inv := fun x => by cases x <;> rfl }

/-- A tape cell: an input symbol `some (Sum.inl t)`, a work cell `some (Sum.inr γ)`, or blank. -/
abbrev KCell := Option (T ⊕ KGamma g₀)

/-- The reverse-rule replacement string for rule `r`: `input_L ++ [N] ++ input_R`
(what `output_string` is rewritten back to). -/
def patList (r : grule T g₀.nt) : List (symbol T g₀.nt) :=
  r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R

/-- The nondeterministic transition relation of the backward simulator. -/
def kTransition : KState g₀ → KCell g₀ → Set (KState g₀ × KCell g₀ × DLBA.Dir) :=
  fun st c => match st, c with
  -- INIT: convert cell 0 (the known left end), marking `isLeftEnd`.
  | .init0, some (Sum.inl t) =>
      {(.initSweep, some (Sum.inr (true, false, some (symbol.terminal t))), .right)}
  | .init0, _ => ∅
  -- INIT sweep: convert each input cell; on the right-end clamp (re-reading a work cell),
  -- mark `isRightEnd` and start the simulation.
  | .initSweep, some (Sum.inl t) =>
      {(.initSweep, some (Sum.inr (false, false, some (symbol.terminal t))), .right)}
  | .initSweep, some (Sum.inr (l, _, ws)) =>
      {(.sim, some (Sum.inr (l, true, ws)), .stay)}
  | .initSweep, _ => ∅
  -- SIM: roam, start the accept check, or start applying any rule backward from here.
  | .sim, some (Sum.inr (l, r, ws)) =>
      {(.sim, some (Sum.inr (l, r, ws)), .left), (.sim, some (Sum.inr (l, r, ws)), .right),
        (.gotoLeft, some (Sum.inr (l, r, ws)), .stay)}
      ∪ {x | ∃ ri : Fin g₀.rules.length, x = (.applyRule ri 0, some (Sum.inr (l, r, ws)), .stay)}
  | .sim, _ => ∅
  -- APPLY a rule backward, single pass: skip blanks; at the `k`-th output symbol, verify the
  -- match and overwrite this cell with the replacement (`patList[k]` if `k < |patList|`, else
  -- blank). On the last symbol, return to `sim`.
  | .applyRule ri k, some (Sum.inr (l, r, none)) =>
      -- blank: skip it (echo, move right), keep the same match position — but never past the
      -- right end (a pass that runs off the tape without completing is dead).
      if r then ∅ else {(.applyRule ri k, some (Sum.inr (l, r, none)), .right)}
  | .applyRule ri k, some (Sum.inr (l, r, some s)) =>
      let rr := g₀.rules[ri]
      let cell : KCell g₀ := some (Sum.inr (l, r, (patList g₀ rr)[k.val]?))
      if rr.output_string[k.val]? = some s then
        -- continuing the pass requires another cell to the right; at the right end (`r`) a pass
        -- with output still remaining is dead. The last symbol may sit on the right end.
        (if k.val + 1 < rr.output_string.length then
            (if r then ∅ else {(.applyRule ri (k + 1), cell, .right)})
          else if k.val + 1 = rr.output_string.length then {(.sim, cell, .right)}
          else ∅)
      else ∅
  | .applyRule _ _, _ => ∅
  -- ACCEPT CHECK: go to the marked left end, then sweep right verifying exactly `[S]`.
  | .gotoLeft, some (Sum.inr (l, r, ws)) =>
      if l then {(.check false, some (Sum.inr (l, r, ws)), .stay)}
      else {(.gotoLeft, some (Sum.inr (l, r, ws)), .left)}
  | .gotoLeft, _ => ∅
  | .check seen, some (Sum.inr (l, r, ws)) =>
      match ws with
      | none =>
          if r then (if seen then {(.accept, some (Sum.inr (l, r, ws)), .stay)} else ∅)
          else {(.check seen, some (Sum.inr (l, r, ws)), .right)}
      | some (symbol.nonterminal N) =>
          if N = g₀.initial ∧ ¬ seen then
            (if r then {(.accept, some (Sum.inr (l, r, ws)), .stay)}
              else {(.check true, some (Sum.inr (l, r, ws)), .right)})
          else ∅
      | some (symbol.terminal _) => ∅
  | .check _, _ => ∅
  | .accept, _ => ∅

/-- The simulating LBA: backward-reduce the input to the start symbol. -/
def kMachine : LBA.Machine (KCell g₀) (KState g₀) where
  transition := kTransition g₀
  accept := fun s => decide (s = KState.accept)
  initial := KState.init0

end Machine

/-! ### Decoding the work track

`formOf` reads the sentential form represented on the tape: the non-blank work symbols, in
cell order. The simulation invariant is phrased in terms of `formOf`. -/
section Form

variable (g₀ : grammar T)

/-- The sentential form represented by a tape's work track: the non-blank work symbols, in
cell order. -/
def formOf {n : ℕ} (c : Fin (n + 1) → KGamma g₀) : List (symbol T g₀.nt) :=
  (List.ofFn c).filterMap (fun γ => γ.2.2)

@[simp] lemma formOf_def {n : ℕ} (c : Fin (n + 1) → KGamma g₀) :
    formOf g₀ c = (List.ofFn c).filterMap (fun γ => γ.2.2) := rfl

/-- If every cell carries a (non-blank) work symbol given by `f`, the form is exactly `ofFn f`. -/
lemma formOf_of_forall_some {n : ℕ} (c : Fin (n + 1) → KGamma g₀)
    (f : Fin (n + 1) → symbol T g₀.nt) (h : ∀ i, (c i).2.2 = some (f i)) :
    formOf g₀ c = List.ofFn f := by
  induction n with
  | zero =>
      simp only [formOf, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, List.filterMap_nil,
        h 0]
  | succ m ih =>
      rw [formOf, List.ofFn_succ]
      simp only [List.filterMap_cons, h 0]
      conv_rhs => rw [List.ofFn_succ]
      congr 1
      exact ih (fun i => c i.succ) (fun i => f i.succ) (fun i => h i.succ)

/-- Updating one value of a finite function corresponds to `List.set` on its `ofFn` list. -/
lemma ofFn_update {α : Type*} {n : ℕ} (W : Fin (n + 1) → α) (i : Fin (n + 1)) (x : α) :
    List.ofFn (Function.update W i x) = (List.ofFn W).set i.val x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj' : j < n + 1 := by rw [List.length_ofFn] at h1; exact h1
    rw [List.getElem_ofFn, List.getElem_set]
    by_cases hj : i.val = j
    · rw [if_pos hj, show (⟨j, hj'⟩ : Fin (n + 1)) = i from Fin.ext hj.symm, Function.update_self]
    · rw [if_neg hj, List.getElem_ofFn,
        Function.update_of_ne (fun he => hj (congrArg Fin.val he).symm)]

/-- The sentential form represented by a *work function* `W` (the marked tape is `mkCell ∘ W`):
the non-blank work symbols, in order. This is what the simulation tracks: after init the tape is
always `mkCell ∘ W`, and `applyRule` updates `W`. -/
def formW {n : ℕ} (W : Fin (n + 1) → KWork g₀) : List (symbol T g₀.nt) :=
  (List.ofFn W).filterMap id

/-- If every work cell is non-blank (`W i = some (f i)`), the form is exactly `ofFn f`. -/
lemma formW_of_forall_some {n : ℕ} (W : Fin (n + 1) → KWork g₀)
    (f : Fin (n + 1) → symbol T g₀.nt) (h : ∀ i, W i = some (f i)) :
    formW g₀ W = List.ofFn f := by
  induction n with
  | zero =>
      simp only [formW, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, List.filterMap_nil,
        h 0, id]
  | succ m ih =>
      rw [formW, List.ofFn_succ]
      simp only [List.filterMap_cons, h 0, id]
      conv_rhs => rw [List.ofFn_succ]
      congr 1
      exact ih (fun i => W i.succ) (fun i => f i.succ) (fun i => h i.succ)

/-- `[L[i]?].filterMap id ++ L.drop (i+1) = L.drop i` — peeling the `i`-th element of a list. -/
lemma cons_getElem?_filterMap_drop {α : Type*} (L : List α) (i : ℕ) :
    ([L[i]?].filterMap id) ++ L.drop (i + 1) = L.drop i := by
  by_cases hi : i < L.length
  · rw [List.getElem?_eq_getElem hi]
    simp only [List.filterMap_cons, id, List.filterMap_nil, List.singleton_append]
    exact (List.drop_eq_getElem_cons hi).symm
  · rw [List.getElem?_eq_none (by omega), List.drop_eq_nil_of_le (by omega),
      List.drop_eq_nil_of_le (by omega)]
    simp

/-- The form decomposes along any tape split point: `formW = filterMap(take a) ++ filterMap(drop a)`. -/
lemma formW_split {n : ℕ} (W : Fin (n + 1) → KWork g₀) (a : ℕ) :
    formW g₀ W = (((List.ofFn W).take a).filterMap id) ++ (((List.ofFn W).drop a).filterMap id) := by
  rw [formW, ← List.filterMap_append, List.take_append_drop]

/-- Reading the non-blank tail at a blank cell: the blank contributes nothing. -/
lemma drop_filterMap_blank {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1))
    (hb : W i = none) :
    ((List.ofFn W).drop i.val).filterMap id = ((List.ofFn W).drop (i.val + 1)).filterMap id := by
  have hlen : i.val < (List.ofFn W).length := by rw [List.length_ofFn]; exact i.isLt
  rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
  simp only [Fin.eta, hb, List.filterMap_cons, id]

/-- Reading the non-blank tail at a symbol cell: the symbol is the head. -/
lemma drop_filterMap_some {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1))
    (s : symbol T g₀.nt) (hs : W i = some s) :
    ((List.ofFn W).drop i.val).filterMap id = s :: ((List.ofFn W).drop (i.val + 1)).filterMap id := by
  have hlen : i.val < (List.ofFn W).length := by rw [List.length_ofFn]; exact i.isLt
  rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
  simp only [Fin.eta, hs, List.filterMap_cons, id]

/-- A backward rule-write `output_string ↦ patList` (in any context) is exactly one *forward*
grammar step `… patList … → … output_string …`. The soundness invariant prepends this step. -/
lemma grammar_transforms_patList {r : grule T g₀.nt} (hr : r ∈ g₀.rules)
    (u v : List (symbol T g₀.nt)) :
    grammar_transforms g₀ (u ++ patList g₀ r ++ v) (u ++ r.output_string ++ v) :=
  ⟨r, hr, u, v, by simp [patList, List.append_assoc], rfl⟩

end Form

/-! ### Step-level glue -/
section Step

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- The only accepting state is `accept`. -/
@[simp] lemma kMachine_accept_iff (s : KState g₀) :
    (kMachine g₀).accept s = true ↔ s = KState.accept := by
  simp [kMachine]

/-- Build one `Step` of `kMachine` from a transition membership. -/
lemma kStep_mk {n : ℕ} {cfg : DLBA.Cfg (KCell g₀) (KState g₀) n} {q' : KState g₀}
    {a : KCell g₀} {d : DLBA.Dir}
    (hmem : (q', a, d) ∈ kTransition g₀ cfg.state cfg.tape.read) :
    LBA.Step (kMachine g₀) cfg ⟨q', (cfg.tape.write a).moveHead d⟩ :=
  ⟨q', a, d, hmem, rfl⟩

/-- Reaching an `accept`-state configuration witnesses acceptance. -/
lemma kAccepts_of_reaches {n : ℕ} {cfg cfg' : DLBA.Cfg (KCell g₀) (KState g₀) n}
    (h : LBA.Reaches (kMachine g₀) cfg cfg') (hacc : cfg'.state = KState.accept) :
    LBA.Accepts (kMachine g₀) cfg :=
  ⟨cfg', h, by simp [kMachine, hacc]⟩

/-- An *echo* step that moves the head left by one, leaving the tape contents unchanged
(the transition rewrites the current cell to its own value). -/
lemma kStep_echo_left {n : ℕ} {c : Fin (n + 1) → KCell g₀} {i : Fin (n + 1)}
    {st st' : KState g₀} (hpos : 0 < i.val)
    (hmem : (st', c i, DLBA.Dir.left) ∈ kTransition g₀ st (c i)) :
    LBA.Step (kMachine g₀) ⟨st, ⟨c, i⟩⟩ ⟨st', ⟨c, ⟨i.val - 1, by omega⟩⟩⟩ := by
  refine ⟨st', c i, DLBA.Dir.left, hmem, ?_⟩
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self,
    dif_pos hpos]

/-- An *echo* step that moves the head right by one, leaving the tape contents unchanged. -/
lemma kStep_echo_right {n : ℕ} {c : Fin (n + 1) → KCell g₀} {i : Fin (n + 1)}
    {st st' : KState g₀} (hlt : i.val < n)
    (hmem : (st', c i, DLBA.Dir.right) ∈ kTransition g₀ st (c i)) :
    LBA.Step (kMachine g₀) ⟨st, ⟨c, i⟩⟩ ⟨st', ⟨c, ⟨i.val + 1, by omega⟩⟩⟩ := by
  refine ⟨st', c i, DLBA.Dir.right, hmem, ?_⟩
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self,
    dif_pos hlt]

/-- An *echo* step that keeps the head in place, leaving the tape contents unchanged. -/
lemma kStep_echo_stay {n : ℕ} {c : Fin (n + 1) → KCell g₀} {i : Fin (n + 1)}
    {st st' : KState g₀} (hmem : (st', c i, DLBA.Dir.stay) ∈ kTransition g₀ st (c i)) :
    LBA.Step (kMachine g₀) ⟨st, ⟨c, i⟩⟩ ⟨st', ⟨c, i⟩⟩ := by
  refine ⟨st', c i, DLBA.Dir.stay, hmem, ?_⟩
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self]

/-- The tape carries correct boundary markers: cell `k` records `isLeftEnd = (k = 0)` and
`isRightEnd = (k = n)`. -/
def Marked {n : ℕ} (c : Fin (n + 1) → KCell g₀) : Prop :=
  ∀ k : Fin (n + 1), ∃ ws : KWork g₀,
    c k = some (Sum.inr (decide (k.val = 0), decide (k.val = n), ws))

/-- The `gotoLeft` sweep: from any head position, echo-move left to the marked left end (cell 0)
and enter the accept check. -/
lemma gotoLeft_reaches {n : ℕ} {c : Fin (n + 1) → KCell g₀} (hmark : Marked g₀ c)
    (i : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.gotoLeft, ⟨c, i⟩⟩ ⟨KState.check false, ⟨c, 0⟩⟩ := by
  suffices H : ∀ m : ℕ, ∀ i : Fin (n + 1), i.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.gotoLeft, ⟨c, i⟩⟩ ⟨KState.check false, ⟨c, 0⟩⟩ from
    H i.val i rfl
  intro m
  induction m with
  | zero =>
      intro i hi
      obtain ⟨ws, hci⟩ := hmark i
      obtain rfl : i = 0 := Fin.ext (by simpa using hi)
      apply Relation.ReflTransGen.single
      apply kStep_echo_stay
      rw [hci]
      simp [kTransition]
  | succ k ih =>
      intro i hi
      obtain ⟨ws, hci⟩ := hmark i
      have hlt : i.val < n + 1 := i.isLt
      have hpos : 0 < i.val := by omega
      have hd0 : decide (i.val = 0) = false := decide_eq_false (by omega)
      have hval : i.val - 1 = k := by omega
      refine Relation.ReflTransGen.head (kStep_echo_left g₀ hpos (st' := KState.gotoLeft) ?_) ?_
      · rw [hci, hd0]; simp [kTransition]
      · exact ih ⟨i.val - 1, by omega⟩ hval

/-- A canonical marked work cell at position `k` carrying work symbol `ws`. -/
def mkCell {n : ℕ} (k : Fin (n + 1)) (ws : KWork g₀) : KCell g₀ :=
  some (Sum.inr (decide (k.val = 0), decide (k.val = n), ws))

/-- The canonical tape built from a work-symbol function is `Marked`. -/
lemma marked_mkTape {n : ℕ} (W : Fin (n + 1) → KWork g₀) :
    Marked g₀ (fun k => mkCell g₀ k (W k)) := fun k => ⟨W k, rfl⟩

/-- Updating one cell of a canonical tape with `mkCell i x` corresponds to updating the work
function at `i`. -/
lemma update_mkCell {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (x : KWork g₀) :
    Function.update (fun k => mkCell g₀ k (W k)) i (mkCell g₀ i x)
      = fun k => mkCell g₀ k (Function.update W i x k) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp only [Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

/-- The accept-check sweep: if the work track spells exactly `[S]` (one cell `j` holds the start
symbol, all others blank), the check started at any cell `i` (with the `seen` flag tracking
whether `j` is behind `i`) reaches the accepting state. -/
lemma check_sweep {n : ℕ} (W : Fin (n + 1) → KWork g₀) (j : Fin (n + 1))
    (hj : W j = some (symbol.nonterminal g₀.initial)) (hother : ∀ k, k ≠ j → W k = none)
    (i : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀)
      ⟨KState.check (decide (j.val < i.val)), ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.accept, ⟨fun k => mkCell g₀ k (W k), Fin.last n⟩⟩ := by
  suffices H : ∀ d, ∀ i : Fin (n + 1), n - i.val = d →
      LBA.Reaches (kMachine g₀)
        ⟨KState.check (decide (j.val < i.val)), ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.accept, ⟨fun k => mkCell g₀ k (W k), Fin.last n⟩⟩ from H (n - i.val) i rfl
  intro d
  induction d with
  | zero =>
      intro i hi
      have hin : i.val = n := by have := i.isLt; omega
      obtain rfl : i = Fin.last n := Fin.ext (by simp [Fin.last, hin])
      apply Relation.ReflTransGen.single
      apply kStep_echo_stay
      by_cases hij : (Fin.last n) = j
      · rw [← hij]
        simp only [mkCell, hij.symm ▸ hj, Fin.val_last, decide_eq_true_eq]
        have : ¬ (j.val < n) := by rw [← hij]; simp
        simp [kTransition, this]
      · have hwn : W (Fin.last n) = none := hother _ hij
        have hjlt : j.val < n := by
          have := j.isLt; rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp j.isLt) with h | h
          · exact h
          · exact absurd (Fin.ext (by simp [Fin.last, h])) hij
        simp only [mkCell, hwn, Fin.val_last]
        simp [kTransition, hjlt]
  | succ e ih =>
      intro i hi
      have hlt : i.val < n := by have := i.isLt; omega
      have hr : decide (i.val = n) = false := decide_eq_false (by omega)
      have he : n - (i.val + 1) = e := by omega
      by_cases hij : i = j
      · -- the start symbol is here; mark it seen and move on
        have hwi : W i = some (symbol.nonterminal g₀.initial) := by rw [hij]; exact hj
        have hseen : decide (j.val < i.val) = false := by rw [hij]; simp
        have hb : decide (j.val < i.val + 1) = true := by rw [hij]; simp
        refine Relation.ReflTransGen.head
          (kStep_echo_right g₀ hlt (st' := KState.check true) ?_)
          (hb ▸ ih ⟨i.val + 1, by omega⟩ he)
        simp only [mkCell, hwi, hr, hseen]; simp [kTransition]
      · -- a blank; keep the flag and move on
        have hwi : W i = none := hother _ hij
        have heq : decide (j.val < i.val + 1) = decide (j.val < i.val) := by
          have hne : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
          simp only [decide_eq_decide]; omega
        refine Relation.ReflTransGen.head
          (kStep_echo_right g₀ hlt (st' := KState.check (decide (j.val < i.val))) ?_)
          (heq ▸ ih ⟨i.val + 1, by omega⟩ he)
        simp only [mkCell, hwi, hr]; simp [kTransition]

/-- If the work track spells exactly `[S]`, the simulator accepts (from any head position):
roam to the left end and run the accept-check sweep. -/
lemma accept_from_S {n : ℕ} (W : Fin (n + 1) → KWork g₀) (j : Fin (n + 1))
    (hj : W j = some (symbol.nonterminal g₀.initial)) (hother : ∀ k, k ≠ j → W k = none)
    (i : Fin (n + 1)) :
    LBA.Accepts (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩ := by
  refine kAccepts_of_reaches g₀
    (cfg' := ⟨KState.accept, ⟨fun k => mkCell g₀ k (W k), Fin.last n⟩⟩) ?_ rfl
  refine Relation.ReflTransGen.head (kStep_echo_stay g₀ (st' := KState.gotoLeft) ?_) ?_
  · simp only [mkCell]; simp [kTransition]
  · refine (gotoLeft_reaches g₀ (marked_mkTape g₀ W) i).trans ?_
    have hsweep := check_sweep g₀ W j hj hother (0 : Fin (n + 1))
    simpa using hsweep

end Step

/-! ### The init conversion sweep -/
section Init

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- Cell `k` converted to a work cell holding `terminal (input k)`, with `isRightEnd = false`
(the right-end bit is set later, on the clamp). -/
def tmpCell {n : ℕ} (input : Fin (n + 1) → T) (k : Fin (n + 1)) : KCell g₀ :=
  some (Sum.inr (decide (k.val = 0), false, some (symbol.terminal (input k))))

/-- The tape with cells `< i` converted, the rest still raw input `some (Sum.inl _)`. -/
def cAt {n : ℕ} (input : Fin (n + 1) → T) (i : ℕ) (k : Fin (n + 1)) : KCell g₀ :=
  if k.val < i then tmpCell g₀ input k else some (Sum.inl (input k))

/-- Converting cell `i` updates `cAt … i` to `cAt … (i+1)`. -/
lemma cAt_update {n : ℕ} (input : Fin (n + 1) → T) (i : Fin (n + 1)) :
    Function.update (cAt g₀ input i.val) i (tmpCell g₀ input i) = cAt g₀ input (i.val + 1) := by
  funext k
  rw [Function.update_apply]
  by_cases hk : k = i
  · subst hk; simp [cAt]
  · have hkv : k.val ≠ i.val := fun h => hk (Fin.ext h)
    rw [if_neg hk]
    simp only [cAt]
    by_cases hki : k.val < i.val
    · rw [if_pos hki, if_pos (by omega)]
    · rw [if_neg hki, if_neg (by omega)]

/-- The transition-membership for converting an input cell `i ≠ 0`. -/
lemma kConvert_mem {n : ℕ} (input : Fin (n + 1) → T) (i : Fin (n + 1))
    (hd0 : decide (i.val = 0) = false) (d : DLBA.Dir) :
    (KState.initSweep, tmpCell g₀ input i, d) ∈
      kTransition g₀ KState.initSweep (cAt g₀ input i.val i) ↔ d = DLBA.Dir.right := by
  rw [show cAt g₀ input i.val i = some (Sum.inl (input i)) from by
    simp only [cAt, if_neg (lt_irrefl _)]]
  simp only [tmpCell, hd0]
  simp [kTransition]

/-- One conversion step (interior cell `i ≠ 0`, `i < n`): convert and move right. -/
lemma kStep_convert_right {n : ℕ} (input : Fin (n + 1) → T) (i : Fin (n + 1))
    (hd0 : decide (i.val = 0) = false) (hlt : i.val < n) :
    LBA.Step (kMachine g₀) ⟨KState.initSweep, ⟨cAt g₀ input i.val, i⟩⟩
      ⟨KState.initSweep, ⟨cAt g₀ input (i.val + 1), ⟨i.val + 1, by omega⟩⟩⟩ := by
  refine ⟨KState.initSweep, tmpCell g₀ input i, DLBA.Dir.right,
    (kConvert_mem g₀ input i hd0 _).2 rfl, ?_⟩
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt, cAt_update]

/-- The last conversion step (cell `n`): convert; moving right clamps, staying at `n`. -/
lemma kStep_convert_last {n : ℕ} (input : Fin (n + 1) → T) (i : Fin (n + 1))
    (hd0 : decide (i.val = 0) = false) (hin : i.val = n) :
    LBA.Step (kMachine g₀) ⟨KState.initSweep, ⟨cAt g₀ input i.val, i⟩⟩
      ⟨KState.initSweep, ⟨cAt g₀ input (i.val + 1), i⟩⟩ := by
  have hmv : ¬ i.val < n := by omega
  refine ⟨KState.initSweep, tmpCell g₀ input i, DLBA.Dir.right,
    (kConvert_mem g₀ input i hd0 _).2 rfl, ?_⟩
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_neg hmv, cAt_update]

/-- The conversion sweep: from cell `i ≥ 1` (with cells `< i` converted), convert the rest of the
input left-to-right, ending (after the right-end clamp) at the fully-converted tape on cell `n`. -/
lemma convert_sweep {n : ℕ} (input : Fin (n + 1) → T) :
    ∀ i : Fin (n + 1), 1 ≤ i.val → LBA.Reaches (kMachine g₀)
      ⟨KState.initSweep, ⟨cAt g₀ input i.val, i⟩⟩
      ⟨KState.initSweep, ⟨cAt g₀ input (n + 1), Fin.last n⟩⟩ := by
  suffices H : ∀ d, ∀ i : Fin (n + 1), 1 ≤ i.val → n - i.val = d → LBA.Reaches (kMachine g₀)
      ⟨KState.initSweep, ⟨cAt g₀ input i.val, i⟩⟩
      ⟨KState.initSweep, ⟨cAt g₀ input (n + 1), Fin.last n⟩⟩ from
    fun i hi1 => H (n - i.val) i hi1 rfl
  intro d
  induction d with
  | zero =>
      intro i hi1 hi
      have hin : i.val = n := by have := i.isLt; omega
      have hd0 : decide (i.val = 0) = false := decide_eq_false (by omega)
      have hil : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      have heq : (⟨KState.initSweep, ⟨cAt g₀ input (i.val + 1), i⟩⟩ :
            DLBA.Cfg (KCell g₀) (KState g₀) n)
          = ⟨KState.initSweep, ⟨cAt g₀ input (n + 1), Fin.last n⟩⟩ := by
        rw [hil]; simp only [Fin.val_last]
      exact Relation.ReflTransGen.single (heq ▸ kStep_convert_last g₀ input i hd0 hin)
  | succ e ih =>
      intro i hi1 hi
      have hlt : i.val < n := by omega
      have hd0 : decide (i.val = 0) = false := decide_eq_false (by omega)
      have h1 : 1 ≤ i.val + 1 := by omega
      have he : n - (i.val + 1) = e := by omega
      exact Relation.ReflTransGen.head (kStep_convert_right g₀ input i hd0 hlt)
        (ih ⟨i.val + 1, by omega⟩ h1 he)

/-- After converting all cells, `cAt … (n+1)` is the fully-converted tape. -/
lemma cAt_full {n : ℕ} (input : Fin (n + 1) → T) :
    cAt g₀ input (n + 1) = tmpCell g₀ input := by
  funext k; simp only [cAt]; rw [if_pos k.isLt]

/-- Configuration equality from component equalities (no `@[ext]` on `Cfg`/`BoundedTape`). -/
lemma cfg_eq {n : ℕ} {s s' : KState g₀} {c c' : Fin (n + 1) → KCell g₀} {h h' : Fin (n + 1)}
    (hs : s = s') (hc : c = c') (hh : h = h') :
    (⟨s, ⟨c, h⟩⟩ : DLBA.Cfg (KCell g₀) (KState g₀) n) = ⟨s', ⟨c', h'⟩⟩ := by
  subst hs; subst hc; subst hh; rfl

/-- The init phase up to the right-end clamp: from the raw input tape (state `init0`, head 0),
reach the fully-converted (`isRightEnd = false`) tape at cell `n`. -/
lemma init_to_tmpCell {n : ℕ} (input : Fin (n + 1) → T) :
    LBA.Reaches (kMachine g₀) ⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, n.succ_pos⟩⟩⟩
      ⟨KState.initSweep, ⟨tmpCell g₀ input, Fin.last n⟩⟩ := by
  have hmem0 : (KState.initSweep, tmpCell g₀ input ⟨0, n.succ_pos⟩, DLBA.Dir.right) ∈
      kTransition g₀ KState.init0 (cAt g₀ input 0 ⟨0, n.succ_pos⟩) := by
    rw [show cAt g₀ input 0 ⟨0, n.succ_pos⟩ = some (Sum.inl (input ⟨0, n.succ_pos⟩)) from by
      simp [cAt]]
    simp only [tmpCell]; simp [kTransition]
  have hupd : Function.update (cAt g₀ input 0) (⟨0, n.succ_pos⟩ : Fin (n + 1))
      (tmpCell g₀ input ⟨0, n.succ_pos⟩) = cAt g₀ input 1 := cAt_update g₀ input ⟨0, n.succ_pos⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    apply Relation.ReflTransGen.single
    refine ⟨KState.initSweep, tmpCell g₀ input ⟨0, by omega⟩, DLBA.Dir.right, hmem0, ?_⟩
    have hmv : ¬ (0 : ℕ) < 0 := by omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_neg hmv]
    refine cfg_eq g₀ rfl ?_ (Fin.ext (by simp [Fin.last]))
    rw [hupd]; exact (cAt_full g₀ input).symm
  · refine Relation.ReflTransGen.head
      (b := ⟨KState.initSweep, ⟨cAt g₀ input 1, ⟨1, by omega⟩⟩⟩) ?_ ?_
    · refine ⟨KState.initSweep, tmpCell g₀ input ⟨0, n.succ_pos⟩, DLBA.Dir.right, hmem0, ?_⟩
      simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hn]
      exact cfg_eq g₀ rfl hupd.symm (Fin.ext rfl)
    · have h1 : (1 : ℕ) ≤ 1 := le_refl 1
      have hcv := convert_sweep g₀ input ⟨1, by omega⟩ h1
      rwa [cAt_full] at hcv

/-- The full init phase: from the raw input tape, reach the canonical marked work tape (state
`sim`), whose work track holds `terminal (input k)` at every cell (so `formOf = input.map`). -/
lemma init_reaches {n : ℕ} (input : Fin (n + 1) → T) :
    ∃ h : Fin (n + 1), LBA.Reaches (kMachine g₀)
      ⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, n.succ_pos⟩⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (some (symbol.terminal (input k))), h⟩⟩ := by
  have hmem : (KState.sim, mkCell g₀ (Fin.last n) (some (symbol.terminal (input (Fin.last n)))),
      DLBA.Dir.stay) ∈ kTransition g₀ KState.initSweep (tmpCell g₀ input (Fin.last n)) := by
    simp only [tmpCell, mkCell, Fin.val_last]; simp [kTransition]
  have htape : (DLBA.BoundedTape.write ⟨tmpCell g₀ input, Fin.last n⟩
      (mkCell g₀ (Fin.last n) (some (symbol.terminal (input (Fin.last n)))))).contents
      = fun k => mkCell g₀ k (some (symbol.terminal (input k))) := by
    funext k
    simp only [DLBA.BoundedTape.write, Function.update_apply]
    by_cases hk : k = Fin.last n
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
      have hkn : k.val ≠ n := fun h => hk (Fin.ext (by simp only [Fin.val_last]; exact h))
      simp only [tmpCell, mkCell, decide_eq_false hkn]
  refine ⟨Fin.last n, (init_to_tmpCell g₀ input).tail ?_⟩
  refine ⟨KState.sim, mkCell g₀ (Fin.last n) (some (symbol.terminal (input (Fin.last n)))),
    DLBA.Dir.stay, hmem, ?_⟩
  simp only [DLBA.BoundedTape.moveHead]
  exact cfg_eq g₀ rfl htape.symm rfl

end Init

/-! ### `applyRule` single-pass steps -/
section Apply

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- Every element of a `ℕ`-list is `≤` its `foldr max 0`. -/
lemma le_foldr_max (L : List ℕ) (x : ℕ) (hx : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at hx
  | cons a t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- Each rule's output length is within `ruleBound`. -/
lemma output_length_le_ruleBound (ri : Fin g₀.rules.length) :
    (g₀.rules[ri]).output_string.length ≤ ruleBound g₀ := by
  apply le_foldr_max
  exact List.mem_map.mpr ⟨g₀.rules[ri], List.getElem_mem _, rfl⟩

/-- From `sim`, begin applying rule `ri` at the current cell (echo, stay). -/
lemma kStep_sim_applyRule {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (l r : Bool) (ws : KWork g₀) (hc : c i = some (Sum.inr (l, r, ws))) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨c, i⟩⟩ ⟨KState.applyRule ri 0, ⟨c, i⟩⟩ := by
  refine kStep_echo_stay g₀ (st' := KState.applyRule ri 0) ?_
  rw [hc]
  simp only [kTransition, Set.mem_union, Set.mem_setOf_eq]
  exact Or.inr ⟨ri, rfl⟩

/-- Skip a blank during the rule-application pass (echo, move right, keep the match position). -/
lemma kStep_applyRule_blank {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (hlt : i.val < n)
    (hc : c i = some (Sum.inr (l, r, none))) (hr : r = false) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.applyRule ri k, ⟨c, ⟨i.val + 1, by omega⟩⟩⟩ := by
  subst hr
  refine kStep_echo_right g₀ hlt (st' := KState.applyRule ri k) ?_
  rw [hc]; simp [kTransition]

/-- Match the `k`-th output symbol and write the replacement, continuing the pass (`k+1 < |out|`). -/
lemma kStep_applyRule_continue {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hlt : i.val < n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 < (g₀.rules[ri]).output_string.length) (hr : r = false) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.applyRule ri (k + 1),
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))),
          ⟨i.val + 1, by omega⟩⟩⟩ := by
  subst hr
  refine ⟨KState.applyRule ri (k + 1),
    some (Sum.inr (l, false, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.applyRule ri (k + 1), some (Sum.inr (l, false, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_pos hk]; simp
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt]

/-- Match the last output symbol (`k+1 = |out|`); the replacement is written and the pass ends
(return to `sim`). -/
lemma kStep_applyRule_last {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hlt : i.val < n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 = (g₀.rules[ri]).output_string.length) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.sim,
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))),
          ⟨i.val + 1, by omega⟩⟩⟩ := by
  have hk' : ¬ k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
  refine ⟨KState.sim,
    some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.sim, some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_neg hk', if_pos hk]; rfl
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt]

/-- Match the last output symbol when the cell is the rightmost (`i.val = n`); moving right
clamps, so the head stays at `n`. -/
lemma kStep_applyRule_last_clamp {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hin : i.val = n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 = (g₀.rules[ri]).output_string.length) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.sim,
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))), i⟩⟩ := by
  have hk' : ¬ k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
  have hmv : ¬ i.val < n := by omega
  refine ⟨KState.sim,
    some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.sim, some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_neg hk', if_pos hk]; rfl
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_neg hmv]

/-- **The rule-application pass** (contiguous window). From `applyRule ri k` at cell `start+k`,
where the window holds `output_string[k..]`, scan to the end writing the replacement, reaching
`sim` with the work function updated on `[start+k, start+q)` to `patList[·]?`. -/
lemma applyRule_pass {n : ℕ} (ri : Fin g₀.rules.length)
    (start : ℕ) (hq : start + (g₀.rules[ri]).output_string.length ≤ n + 1) :
    ∀ d : ℕ, ∀ (W : Fin (n + 1) → KWork g₀) (k : Fin (ruleBound g₀ + 1))
      (hk : k.val < (g₀.rules[ri]).output_string.length)
      (_ : (g₀.rules[ri]).output_string.length - 1 - k.val = d)
      (_ : ∀ j, k.val ≤ j → ∀ (hj : j < (g₀.rules[ri]).output_string.length),
        W ⟨start + j, by omega⟩ = some ((g₀.rules[ri]).output_string[j])),
      ∃ h : Fin (n + 1), LBA.Reaches (kMachine g₀)
        ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨start + k.val, by omega⟩⟩⟩
        ⟨KState.sim, ⟨fun p => mkCell g₀ p
          (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
            then (patList g₀ g₀.rules[ri])[p.val - start]? else W p), h⟩⟩ := by
  intro d
  induction d with
  | zero =>
      intro W k hk hd hmatch
      have hkq : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
      have hW : W ⟨start + k.val, by omega⟩ = some ((g₀.rules[ri]).output_string[k.val]) :=
        hmatch k.val (le_refl _) hk
      have hc : (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          = some (Sum.inr (decide ((start + k.val) = 0), decide ((start + k.val) = n),
              some ((g₀.rules[ri]).output_string[k.val]))) := by
        simp only [mkCell]; rw [hW]
      have hm : (g₀.rules[ri]).output_string[k.val]? = some ((g₀.rules[ri]).output_string[k.val]) :=
        List.getElem?_eq_getElem hk
      have hWset : ∀ p : Fin (n + 1),
          (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
            then (patList g₀ g₀.rules[ri])[p.val - start]? else W p)
          = Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
              ((patList g₀ g₀.rules[ri])[k.val]?) p := by
        intro p
        rw [Function.update_apply]
        by_cases hp : p.val = start + k.val
        · rw [if_pos (Fin.ext hp), if_pos ⟨by omega, by omega⟩]
          congr 1; omega
        · rw [if_neg (fun he => hp (congrArg Fin.val he)), if_neg (by rintro ⟨h1, h2⟩; omega)]
      have htape : (fun p => mkCell g₀ p
            (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]? else W p))
          = Function.update (fun p => mkCell g₀ p (W p)) (⟨start + k.val, by omega⟩ : Fin (n + 1))
              (mkCell g₀ (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?)) := by
        conv_lhs => ext p; rw [hWset p]
        exact (update_mkCell g₀ W ⟨start + k.val, by omega⟩
          ((patList g₀ g₀.rules[ri])[k.val]?)).symm
      by_cases hlt : start + k.val < n
      · refine ⟨⟨start + k.val + 1, by omega⟩, Relation.ReflTransGen.single ?_⟩
        rw [htape]
        exact kStep_applyRule_last g₀ (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          ri k _ _ _ hlt hc hm hkq
      · refine ⟨⟨start + k.val, by omega⟩, Relation.ReflTransGen.single ?_⟩
        rw [htape]
        exact kStep_applyRule_last_clamp g₀ (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          ri k _ _ _ (by show start + k.val = n; omega) hc hm hkq
  | succ e ih =>
      intro W k hk hd hmatch
      have hltq : k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
      have hkrb : k.val + 1 < ruleBound g₀ + 1 := by
        have := output_length_le_ruleBound g₀ ri; omega
      have hW : W ⟨start + k.val, by omega⟩ = some ((g₀.rules[ri]).output_string[k.val]) :=
        hmatch k.val (le_refl _) hk
      have hc : (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          = some (Sum.inr (decide ((start + k.val) = 0), decide ((start + k.val) = n),
              some ((g₀.rules[ri]).output_string[k.val]))) := by
        simp only [mkCell]; rw [hW]
      have hm : (g₀.rules[ri]).output_string[k.val]? = some ((g₀.rules[ri]).output_string[k.val]) :=
        List.getElem?_eq_getElem hk
      have hlt : start + k.val < n := by omega
      have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hstep : LBA.Step (kMachine g₀)
          ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨start + k.val, by omega⟩⟩⟩
          ⟨KState.applyRule ri (k + 1), ⟨fun p => mkCell g₀ p
            (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
              ((patList g₀ g₀.rules[ri])[k.val]?) p), ⟨start + k.val + 1, by omega⟩⟩⟩ := by
        have hcont := kStep_applyRule_continue g₀ (fun p => mkCell g₀ p (W p))
          ⟨start + k.val, by omega⟩ ri k _ _ _ hlt hc hm hltq (by simp; omega)
        rw [show (fun p => mkCell g₀ p (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
              = Function.update (fun p => mkCell g₀ p (W p)) (⟨start + k.val, by omega⟩ : Fin (n + 1))
                  (mkCell g₀ (⟨start + k.val, by omega⟩ : Fin (n + 1))
                    ((patList g₀ g₀.rules[ri])[k.val]?))
            from (update_mkCell g₀ W ⟨start + k.val, by omega⟩
              ((patList g₀ g₀.rules[ri])[k.val]?)).symm]
        exact hcont
      have hmatch1 : ∀ j, (k + 1).val ≤ j → ∀ (hj : j < (g₀.rules[ri]).output_string.length),
          (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
            ((patList g₀ g₀.rules[ri])[k.val]?)) ⟨start + j, by omega⟩
            = some ((g₀.rules[ri]).output_string[j]) := by
        intro j hj1 hj
        rw [hval] at hj1
        rw [Function.update_of_ne (fun he => by have := congrArg Fin.val he; simp only [] at this; omega)]
        exact hmatch j (by omega) hj
      obtain ⟨h, hreach⟩ := ih (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
        ((patList g₀ g₀.rules[ri])[k.val]?)) (k + 1) (by rw [hval]; omega) (by rw [hval]; omega)
        hmatch1
      refine ⟨h, Relation.ReflTransGen.head hstep ?_⟩
      simp only [hval] at hreach
      have hWeq : (fun p => mkCell g₀ p
            (if start + (k.val + 1) ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]?
              else Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
          = (fun p => mkCell g₀ p
            (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]? else W p)) := by
        funext p
        congr 1
        by_cases hp0 : p.val = start + k.val
        · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩,
            Function.update_apply, if_pos (Fin.ext hp0)]
          congr 1; omega
        · by_cases hp1 : start + (k.val + 1) ≤ p.val ∧
              p.val < start + (g₀.rules[ri]).output_string.length
          · rw [if_pos hp1, if_pos ⟨by omega, hp1.2⟩]
          · rw [if_neg hp1, if_neg (by rintro ⟨h1, h2⟩; omega),
              Function.update_of_ne (fun he => hp0 (congrArg Fin.val he))]
      exact (congrArg (LBA.Reaches (kMachine g₀) _) (cfg_eq g₀ rfl hWeq rfl)).mp hreach

/-- **The general rule-application pass** (skips interspersed blanks). From `applyRule ri k` at
cell `pos`, where the non-blank cells from `pos` begin with `output_string[k..]` followed by `v`,
scan right (skipping blanks, matching each output symbol and writing the replacement) and reach
`sim` with the work track's non-blank tail now `patList[k..] ++ v`, leaving cells `< pos` fixed. -/
lemma applyRule_pass_gen {n : ℕ} (ri : Fin g₀.rules.length) (v : List (symbol T g₀.nt))
    (hpat : (patList g₀ g₀.rules[ri]).length ≤ (g₀.rules[ri]).output_string.length) :
    ∀ d : ℕ, ∀ (W : Fin (n + 1) → KWork g₀) (pos : ℕ) (hpn : pos < n + 1)
      (k : Fin (ruleBound g₀ + 1)) (hk : k.val < (g₀.rules[ri]).output_string.length)
      (_ : n - pos = d)
      (_ : ((List.ofFn W).drop pos).filterMap id
            = (g₀.rules[ri]).output_string.drop k.val ++ v),
      ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
        LBA.Reaches (kMachine g₀)
          ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨pos, hpn⟩⟩⟩
          ⟨KState.sim, ⟨fun p => mkCell g₀ p (W' p), h⟩⟩
        ∧ (∀ p : Fin (n + 1), p.val < pos → W' p = W p)
        ∧ ((List.ofFn W').drop pos).filterMap id
            = (patList g₀ g₀.rules[ri]).drop k.val ++ v := by
  intro d
  induction d with
  | zero =>
      intro W pos hpn k hk hd hfm
      have hpos : pos = n := by omega
      have hdropn : (List.ofFn W).drop pos = [W ⟨pos, hpn⟩] := by
        rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn,
          List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega)]
      rw [hdropn] at hfm
      rcases hw : W ⟨pos, hpn⟩ with _ | s
      · rw [hw] at hfm; simp only [List.filterMap_cons, id, List.filterMap_nil] at hfm
        have hz : ((g₀.rules[ri]).output_string.drop k.val).length = 0 := by
          have := congrArg List.length hfm
          simp only [List.length_nil, List.length_append] at this; omega
        rw [List.length_drop] at hz; omega
      · rw [hw] at hfm; simp only [List.filterMap_cons, id, List.filterMap_nil] at hfm
        have hlen : 1 = (g₀.rules[ri]).output_string.length - k.val + v.length := by
          have := congrArg List.length hfm
          simp only [List.length_cons, List.length_nil, List.length_append, List.length_drop] at this
          omega
        have hkq : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
        have hv : v = [] := by
          have : v.length = 0 := by omega
          exact List.length_eq_zero_iff.mp this
        subst hv
        have hm : (g₀.rules[ri]).output_string[k.val]? = some s := by
          have hds : (g₀.rules[ri]).output_string.drop k.val = [s] := by
            rw [← List.append_nil ((g₀.rules[ri]).output_string.drop k.val)]; exact hfm.symm
          have hcons : (g₀.rules[ri]).output_string[k.val]
              :: (g₀.rules[ri]).output_string.drop (k.val + 1) = [s] :=
            (List.drop_eq_getElem_cons hk).symm.trans hds
          rw [List.getElem?_eq_getElem hk]
          simp only [List.cons.injEq] at hcons
          rw [hcons.1]
        have hc : (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            = some (Sum.inr (decide (pos = 0), decide (pos = n), some s)) := by
          simp only [mkCell]; rw [hw]
        refine ⟨Function.update W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?), ⟨pos, hpn⟩,
          Relation.ReflTransGen.single ?_, ?_, ?_⟩
        · have hstep := kStep_applyRule_last_clamp g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            ri k _ _ s hpos hc hm hkq
          rw [show (fun p => mkCell g₀ p (Function.update W ⟨pos, hpn⟩
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
              = Function.update (fun p => mkCell g₀ p (W p)) (⟨pos, hpn⟩ : Fin (n + 1))
                  (mkCell g₀ (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?))
              from (update_mkCell g₀ W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?)).symm]
          exact hstep
        · intro p hp; rw [Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
        · rw [ofFn_update]
          rw [show (((List.ofFn W).set (⟨pos, hpn⟩ : Fin (n + 1)).val
                ((patList g₀ g₀.rules[ri])[k.val]?)).drop pos)
              = [((patList g₀ g₀.rules[ri])[k.val]?)] from by
            rw [show (⟨pos, hpn⟩ : Fin (n + 1)).val = pos from rfl,
              List.drop_eq_getElem_cons (by simpa using hpn),
              List.getElem_set_self,
              List.drop_eq_nil_of_le (by simp; omega)]]
          rw [List.append_nil]
          have h0 := cons_getElem?_filterMap_drop (patList g₀ g₀.rules[ri]) k.val
          rwa [List.drop_eq_nil_of_le (show (patList g₀ g₀.rules[ri]).length ≤ k.val + 1 by omega),
            List.append_nil] at h0
  | succ e ih =>
      intro W pos hpn k hk hd hfm
      have hlt : pos < n := by omega
      rcases hw : W ⟨pos, hpn⟩ with _ | s
      · -- blank: skip
        have hfm' : ((List.ofFn W).drop (pos + 1)).filterMap id
            = (g₀.rules[ri]).output_string.drop k.val ++ v := by
          rw [← drop_filterMap_blank g₀ W ⟨pos, hpn⟩ hw]; exact hfm
        obtain ⟨W', h, hreach, hpre, hsuf⟩ := ih W (pos + 1) (by omega) k hk (by omega) hfm'
        refine ⟨W', h, ?_, ?_, ?_⟩
        · exact Relation.ReflTransGen.head
            (kStep_applyRule_blank g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩ ri k _ _ hlt
              (by simp only [mkCell]; rw [hw]) (by simp; omega)) hreach
        · intro p hp; exact hpre p (by omega)
        · rw [show (List.ofFn W').drop pos = W' ⟨pos, hpn⟩ :: (List.ofFn W').drop (pos + 1) from by
            rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
          rw [hpre ⟨pos, hpn⟩ (Nat.lt_succ_self pos), hw]
          simp only [List.filterMap_cons, id]
          exact hsuf
      · -- symbol: match and write
        have hds := drop_filterMap_some g₀ W ⟨pos, hpn⟩ s hw
        rw [hfm] at hds
        -- hds : output.drop k.val ++ v = s :: ((ofFn W).drop (pos+1)).filterMap id
        have hsk : (g₀.rules[ri]).output_string[k.val] = s ∧
            ((List.ofFn W).drop (pos + 1)).filterMap id
              = (g₀.rules[ri]).output_string.drop (k.val + 1) ++ v := by
          rw [show (g₀.rules[ri]).output_string.drop k.val
                = (g₀.rules[ri]).output_string[k.val] :: (g₀.rules[ri]).output_string.drop (k.val + 1)
              from List.drop_eq_getElem_cons hk] at hds
          simp only [List.cons_append, List.cons.injEq] at hds
          exact ⟨hds.1, hds.2.symm⟩
        have hm : (g₀.rules[ri]).output_string[k.val]? = some s := by
          rw [List.getElem?_eq_getElem hk, hsk.1]
        have hc : (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            = some (Sum.inr (decide (pos = 0), decide (pos = n), some s)) := by
          simp only [mkCell]; rw [hw]
        set W₁ := Function.update W (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?)
          with hW₁
        have hbridge : (fun p => mkCell g₀ p (W₁ p))
            = Function.update (fun p => mkCell g₀ p (W p)) (⟨pos, hpn⟩ : Fin (n + 1))
                (mkCell g₀ (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?)) := by
          rw [hW₁]; exact (update_mkCell g₀ W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?)).symm
        have hfm1 : ((List.ofFn W₁).drop (pos + 1)).filterMap id
            = (g₀.rules[ri]).output_string.drop (k.val + 1) ++ v := by
          rw [show (List.ofFn W₁).drop (pos + 1) = (List.ofFn W).drop (pos + 1) from by
            rw [ofFn_update, show (⟨pos, hpn⟩ : Fin (n + 1)).val = pos from rfl]
            apply List.ext_getElem?
            intro j
            rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_set_ne (by omega)]]
          exact hsk.2
        have hW1pos : W₁ ⟨pos, hpn⟩ = (patList g₀ g₀.rules[ri])[k.val]? := by
          rw [hW₁, Function.update_self]
        by_cases hkq : k.val + 1 < (g₀.rules[ri]).output_string.length
        · have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 := by
            apply Fin.val_add_one_of_lt'
            have := output_length_le_ruleBound g₀ ri; omega
          obtain ⟨W', h, hreach, hpre, hsuf⟩ :=
            ih W₁ (pos + 1) (by omega) (k + 1) (by rw [hval]; omega) (by omega)
              (by rw [hval]; exact hfm1)
          refine ⟨W', h, ?_, ?_, ?_⟩
          · refine Relation.ReflTransGen.head ?_ hreach
            have hstep := kStep_applyRule_continue g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
              ri k _ _ s hlt hc hm hkq (by simp; omega)
            rw [hbridge]; exact hstep
          · intro p hp
            rw [hpre p (by omega), hW₁, Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
          · rw [show (List.ofFn W').drop pos = W' ⟨pos, hpn⟩ :: (List.ofFn W').drop (pos + 1) from by
              rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
            rw [hpre ⟨pos, hpn⟩ (Nat.lt_succ_self pos), hW1pos]
            rw [hval] at hsuf
            rw [← List.singleton_append, List.filterMap_append, hsuf, ← List.append_assoc,
              cons_getElem?_filterMap_drop]
        · have hkq' : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
          refine ⟨W₁, ⟨pos + 1, by omega⟩, ?_, ?_, ?_⟩
          · have hstep := kStep_applyRule_last g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
              ri k _ _ s hlt hc hm hkq'
            rw [hbridge]; exact Relation.ReflTransGen.single hstep
          · intro p hp
            rw [hW₁, Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
          · rw [show (List.ofFn W₁).drop pos = W₁ ⟨pos, hpn⟩ :: (List.ofFn W₁).drop (pos + 1) from by
              rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
            rw [hW1pos, ← List.singleton_append, List.filterMap_append, hfm1,
              List.drop_eq_nil_of_le (show (g₀.rules[ri]).output_string.length ≤ k.val + 1 by omega),
              List.nil_append]
            have h0 := cons_getElem?_filterMap_drop (patList g₀ g₀.rules[ri]) k.val
            rw [List.drop_eq_nil_of_le (show (patList g₀ g₀.rules[ri]).length ≤ k.val + 1 by omega),
              List.append_nil] at h0
            rw [h0]

end Apply

/-! ### Replaying a derivation backwards (completeness) -/
section Complete

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- In `sim`, the head may move one cell right (the tape is unchanged). -/
lemma kStep_sim_right {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hlt : i.val < n) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), ⟨i.val + 1, by omega⟩⟩⟩ := by
  refine kStep_echo_right g₀ hlt (st' := KState.sim) ?_
  simp only [mkCell]; simp [kTransition]

/-- In `sim`, the head may move one cell left (the tape is unchanged). -/
lemma kStep_sim_left {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hpos : 0 < i.val) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), ⟨i.val - 1, by omega⟩⟩⟩ := by
  refine kStep_echo_left g₀ hpos (st' := KState.sim) ?_
  simp only [mkCell]; simp [kTransition]

/-- From `sim` at any cell, reach `sim` at the left end (cell 0). -/
lemma sim_reaches_zero {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩ := by
  suffices H : ∀ m, ∀ i : Fin (n + 1), i.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩ from H i.val i rfl
  intro m
  induction m with
  | zero => intro i hi; obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact .refl
  | succ k ih =>
      intro i hi
      have hpos : 0 < i.val := by omega
      exact Relation.ReflTransGen.head (kStep_sim_left g₀ W i hpos)
        (ih ⟨i.val - 1, by omega⟩ (by show i.val - 1 = k; omega))

/-- From `sim` at the left end, reach `sim` at any cell `j` (sweep right). -/
lemma sim_zero_reaches {n : ℕ} (W : Fin (n + 1) → KWork g₀) (j : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ := by
  suffices H : ∀ m, ∀ j : Fin (n + 1), j.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ from H j.val j rfl
  intro m
  induction m with
  | zero => intro j hj; obtain rfl : j = 0 := Fin.ext (by simpa using hj); exact .refl
  | succ k ih =>
      intro j hj
      have hjlt := j.isLt
      have hkn : k < n := by omega
      have hk1 : k + 1 < n + 1 := by omega
      have hjeq : j = (⟨k + 1, hk1⟩ : Fin (n + 1)) := Fin.ext (by simpa using hj)
      rw [hjeq]
      exact (ih ⟨k, by omega⟩ rfl).tail (kStep_sim_right g₀ W ⟨k, by omega⟩ hkn)

/-- From `sim`, the head may be repositioned to any cell. -/
lemma sim_reaches {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i j : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ :=
  (sim_reaches_zero g₀ W i).trans (sim_zero_reaches g₀ W j)

/-- Locate a tape split point realizing a given prefix of the decoded form: if a list of
work cells filters to `u ++ z` with `z` non-empty, some position `p` (a valid cell index)
splits the tape with `u` to the left and `z` to the right. -/
lemma list_split_filterMap {α : Type*} (L : List (Option α)) (u z : List α)
    (h : L.filterMap id = u ++ z) (hz : z ≠ []) :
    ∃ p, p < L.length ∧ (L.take p).filterMap id = u ∧ (L.drop p).filterMap id = z := by
  induction L generalizing u with
  | nil => simp only [List.filterMap_nil] at h; exact absurd (List.append_eq_nil_iff.mp h.symm).2 hz
  | cons a t ih =>
      rcases ha : a with _ | x
      · -- blank head: recurse on the tail, shift the split right by one
        rw [ha] at h; simp only [List.filterMap_cons, id, ha] at h
        obtain ⟨p, hp, ht, hd⟩ := ih u h
        refine ⟨p + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [List.take_succ_cons, List.filterMap_cons, id, ha]; exact ht
        · simp only [List.drop_succ_cons]; exact hd
      · -- symbol head: either it is the first symbol of `z` (`u = []`) or of `u`
        rw [ha] at h; simp only [List.filterMap_cons, id, ha] at h
        cases u with
        | nil =>
            refine ⟨0, by simp only [List.length_cons]; omega, by simp, ?_⟩
            simp only [List.drop_zero, List.filterMap_cons, id, ha]; simpa using h
        | cons b u' =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
            obtain ⟨p, hp, ht, hd⟩ := ih u' h.2
            refine ⟨p + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
            · simp only [List.take_succ_cons, List.filterMap_cons, id, ha, h.1]; rw [ht]
            · simp only [List.drop_succ_cons]; exact hd

/-- **One backward derivation step.** If the work track decodes to `u ++ output ++ v` for some
rule `r` (output non-empty by non-contraction), the simulator can reposition, run one backward
`applyRule` pass, and arrive in `sim` with the track decoding to `u ++ patList r ++ v` — i.e. it
undoes the forward step `u ++ patList r ++ v ⇒ u ++ output ++ v`. -/
lemma step_back {n : ℕ} (hnc : grammar_noncontracting g₀) (W : Fin (n + 1) → KWork g₀)
    (i : Fin (n + 1)) (r : grule T g₀.nt) (hr : r ∈ g₀.rules) (u v : List (symbol T g₀.nt))
    (hform : formW g₀ W = u ++ r.output_string ++ v) :
    ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W' k), h⟩⟩
      ∧ formW g₀ W' = u ++ patList g₀ r ++ v := by
  -- Locate the rule's index and the non-contraction bounds.
  obtain ⟨ri, hri⟩ : ∃ ri : Fin g₀.rules.length, g₀.rules[ri] = r := by
    obtain ⟨idx, hidx, he⟩ := List.getElem_of_mem hr
    exact ⟨⟨idx, hidx⟩, he⟩
  have hncr := hnc r hr
  have hpatlen : (patList g₀ r).length ≤ r.output_string.length := by
    simp only [patList, List.length_append, List.length_cons, List.length_nil] at *; omega
  have houtpos : 0 < r.output_string.length := by omega
  -- Find the split position `p`: `u` to the left, `output ++ v` to the right.
  obtain ⟨p, hp, htake, hdropv⟩ :=
    list_split_filterMap (List.ofFn W) u (r.output_string ++ v)
      (by rw [← List.append_assoc]; exact hform) (by simp [houtpos, List.ne_nil_of_length_pos])
  rw [List.length_ofFn] at hp
  -- Run the backward pass starting at `p` (entered from `sim`).
  obtain ⟨W', h, hreach, hpre, hsuf⟩ :=
    applyRule_pass_gen g₀ ri v (by rw [hri]; exact hpatlen) (n - p) W p hp
      (0 : Fin (ruleBound g₀ + 1)) (by rw [hri]; exact houtpos) rfl
      (by rw [hri]; simpa using hdropv)
  refine ⟨W', h, ?_, ?_⟩
  · -- reposition to `p`, take one `sim → applyRule` step, then the pass.
    refine (sim_reaches g₀ W i ⟨p, hp⟩).trans
      (Relation.ReflTransGen.head
        (kStep_sim_applyRule g₀ (fun k => mkCell g₀ k (W k)) ⟨p, hp⟩ ri _ _ _ rfl) ?_)
    exact hreach
  · -- the decoded form: prefix `u` unchanged, suffix becomes `patList r ++ v`.
    have hagree : (List.ofFn W').take p = (List.ofFn W).take p := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_ofFn]
      · intro j h1 _
        have hjp : j < p := by
          rw [List.length_take, List.length_ofFn] at h1; omega
        simp only [List.getElem_take, List.getElem_ofFn]
        exact hpre ⟨j, by omega⟩ hjp
    simp only [Fin.val_zero, List.drop_zero, hri] at hsuf
    rw [formW_split g₀ W' p, hagree, htake, hsuf, ← List.append_assoc]

/-- **Replaying a whole derivation backwards.** If `β ⇒* γ` and the work track decodes to `γ`,
the simulator reaches `sim` with the track decoding to `β`. -/
lemma derive_back {n : ℕ} (hnc : grammar_noncontracting g₀)
    {β γ : List (symbol T g₀.nt)} (hd : grammar_derives g₀ β γ)
    (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hform : formW g₀ W = γ) :
    ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W' k), h⟩⟩
      ∧ formW g₀ W' = β := by
  induction hd using Relation.ReflTransGen.head_induction_on generalizing W i with
  | refl => exact ⟨W, i, .refl, hform⟩
  | @head a c hac _ ih =>
      obtain ⟨W₁, h₁, hreach₁, hform₁⟩ := ih W i hform
      obtain ⟨r, hr, u, v, hbeq, hceq⟩ := hac
      obtain ⟨W₂, h₂, hreach₂, hform₂⟩ :=
        step_back g₀ hnc W₁ h₁ r hr u v (by rw [hform₁, hceq])
      refine ⟨W₂, h₂, hreach₁.trans hreach₂, ?_⟩
      rw [hform₂, hbeq]; simp only [patList, List.append_assoc]

/-- If the work track decodes to a single symbol `s`, exactly one cell holds it (the rest blank). -/
lemma filterMap_ofFn_singleton {α : Type*} {n : ℕ} (W : Fin (n + 1) → Option α) (s : α)
    (h : (List.ofFn W).filterMap id = [s]) :
    ∃ j : Fin (n + 1), W j = some s ∧ ∀ k, k ≠ j → W k = none := by
  induction n with
  | zero =>
      have hof : List.ofFn W = [W 0] := by simp [List.ofFn_succ, List.ofFn_zero]
      rw [hof] at h
      rcases hw : W 0 with _ | x
      · rw [hw] at h; simp at h
      · rw [hw] at h; simp only [List.filterMap_cons, id, List.filterMap_nil] at h
        obtain rfl : x = s := by simpa using h
        refine ⟨0, hw, fun k hk => ?_⟩
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', _⟩
        · exact absurd rfl hk
        · exact k'.elim0
  | succ m ih =>
      have hof : List.ofFn W = W 0 :: List.ofFn (fun i => W i.succ) := by rw [List.ofFn_succ]
      rw [hof] at h
      rcases hw : W 0 with _ | x
      · rw [hw] at h; simp only [List.filterMap_cons, id, List.filterMap_nil] at h
        obtain ⟨j', hj', hoth'⟩ := ih (fun i => W i.succ) h
        refine ⟨j'.succ, hj', ?_⟩
        intro k hk
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
        · exact hw
        · exact hoth' k' (fun he => hk (by rw [he]))
      · rw [hw] at h; simp only [List.filterMap_cons, id] at h
        obtain ⟨rfl, hnil⟩ : x = s ∧ (List.ofFn (fun i => W i.succ)).filterMap id = [] := by
          simpa using h
        refine ⟨0, hw, ?_⟩
        intro k hk
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
        · exact absurd rfl hk
        · have hmem : W k'.succ ∈ List.ofFn (fun i => W i.succ) := List.mem_ofFn.mpr ⟨k', rfl⟩
          exact List.filterMap_eq_nil_iff.mp hnil _ hmem

end Complete

/-! ### Soundness: a reachable accepting run exhibits a derivation -/
section Sound

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- Decode one tape cell to the sentential-form symbol it represents: a raw input cell
`some (inl t)` decodes to `terminal t` (so the decoded form is unchanged during the init sweep),
a work cell decodes to its work symbol, a blank to nothing. -/
def decodeCell : KCell g₀ → KWork g₀
  | none => none
  | some (Sum.inl t) => some (symbol.terminal t)
  | some (Sum.inr (_, _, ws)) => ws

/-- The sentential form represented by a whole tape (the non-blank decoded cells, in order). -/
def decodeForm {n : ℕ} (c : Fin (n + 1) → KCell g₀) : List (symbol T g₀.nt) :=
  (List.ofFn (fun k => decodeCell g₀ (c k))).filterMap id

@[simp] lemma decodeCell_mkCell {n : ℕ} (k : Fin (n + 1)) (ws : KWork g₀) :
    decodeCell g₀ (mkCell g₀ k ws) = ws := rfl

/-- The decoded form of a canonical work tape is its `formW`. -/
lemma decodeForm_mkCell {n : ℕ} (W : Fin (n + 1) → KWork g₀) :
    decodeForm g₀ (fun k => mkCell g₀ k (W k)) = formW g₀ W := by
  simp only [decodeForm, decodeCell_mkCell, formW]

@[simp] lemma decodeCell_inl (t : T) :
    decodeCell g₀ (some (Sum.inl t)) = some (symbol.terminal t) := rfl

/-- During the init sweep the decoded form is constant: every raw or converted cell of
`cAt input i` decodes to `terminal (input k)`. -/
lemma decodeForm_cAt {n : ℕ} (input : Fin (n + 1) → T) (i : ℕ) :
    decodeForm g₀ (cAt g₀ input i) = List.ofFn (fun k => symbol.terminal (input k)) := by
  have hcell : ∀ k, decodeCell g₀ (cAt g₀ input i k) = some (symbol.terminal (input k)) := by
    intro k
    simp only [cAt]
    by_cases hk : k.val < i
    · rw [if_pos hk]; simp only [tmpCell, decodeCell]
    · rw [if_neg hk]; simp only [decodeCell]
  simp only [decodeForm, hcell]
  rw [show (fun k => some (symbol.terminal (input k))) = (fun k => (some (symbol.terminal (input k)) : KWork g₀)) from rfl]
  rw [← formW]
  exact formW_of_forall_some g₀ _ (fun k => symbol.terminal (input k)) (fun _ => rfl)

/-- `take (i+1)` peels the `i`-th cell off the decoded prefix. -/
lemma take_succ_filterMap {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1)) :
    ((List.ofFn W).take (head.val + 1)).filterMap id
      = ((List.ofFn W).take head.val).filterMap id ++ ([W head].filterMap id) := by
  rw [← List.take_concat_get' (List.ofFn W) head.val (by rw [List.length_ofFn]; exact head.isLt),
    List.filterMap_append, List.getElem_ofFn, Fin.eta]

/-- The decoded form splits at the head into prefix, head cell, and suffix. -/
lemma decodeForm_split_head {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1))
    (pre : List (symbol T g₀.nt))
    (hp : ((List.ofFn W).take head.val).filterMap id = pre) :
    formW g₀ W = pre ++ ([W head].filterMap id)
      ++ ((List.ofFn W).drop (head.val + 1)).filterMap id := by
  have hdc : ((List.ofFn W).drop head.val).filterMap id
      = ([W head].filterMap id) ++ ((List.ofFn W).drop (head.val + 1)).filterMap id := by
    have hlen : head.val < (List.ofFn W).length := by rw [List.length_ofFn]; exact head.isLt
    rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn, Fin.eta, ← List.singleton_append,
      List.filterMap_append]
  conv_lhs => rw [formW, ← List.take_append_drop head.val (List.ofFn W), List.filterMap_append]
  rw [hp, hdc, ← List.append_assoc]

/-- The head-moved tape after an *echo* write at `head` (cell value re-written) with `head.val < n`
is the same canonical tape with the head advanced one cell. -/
lemma echo_moveHead_right {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1))
    (a : KCell g₀) (ha : a = (fun k => mkCell g₀ k (W k)) head) (hlt : head.val < n) :
    (DLBA.BoundedTape.write (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
        a).moveHead DLBA.Dir.right
      = ⟨fun k => mkCell g₀ k (W k), ⟨head.val + 1, by omega⟩⟩ := by
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt, ha,
    Function.update_eq_self]

/-- **Soundness of the accept check** (reverse of `check_sweep`): if a `check` sweep whose verified
prefix spells `[S]` iff `seen` reaches an accepting configuration, the whole track spells `[S]`. -/
lemma check_sound {n : ℕ} {cfgacc : DLBA.Cfg (KCell g₀) (KState g₀) n}
    (hacc : cfgacc.state = KState.accept) (W : Fin (n + 1) → KWork g₀) :
    ∀ d : ℕ, ∀ (seen : Bool) (head : Fin (n + 1)), n - head.val = d →
      LBA.Reaches (kMachine g₀)
        ⟨KState.check seen, ⟨fun k => mkCell g₀ k (W k), head⟩⟩ cfgacc →
      ((List.ofFn W).take head.val).filterMap id
        = (if seen then [symbol.nonterminal g₀.initial] else []) →
      formW g₀ W = [symbol.nonterminal g₀.initial] := by
  intro d
  induction d with
  | zero =>
      intro seen head hd hreach hpre
      have hhn : head.val = n := by have := head.isLt; omega
      have hdrop : ((List.ofFn W).drop (head.val + 1)).filterMap id = [] := by
        rw [List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.filterMap_nil]
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read] at hmem
        rcases hwh : W head with _ | sym
        · -- blank at the right end: accept needs `seen`
          cases seen with
          | false => simp only [mkCell, hwh, hhn, kTransition] at hmem; simp at hmem
          | true => rw [decodeForm_split_head g₀ W head _ hpre, hdrop, hwh]; simp
        · rcases sym with t | N
          · -- terminal: stuck
            simp [mkCell, hwh, kTransition] at hmem
          · -- nonterminal
            cases seen with
            | true => simp only [mkCell, hwh, hhn, kTransition] at hmem; simp at hmem
            | false =>
                by_cases hN : N = g₀.initial
                · subst hN; rw [decodeForm_split_head g₀ W head _ hpre, hdrop, hwh]; simp
                · simp only [mkCell, hwh, hhn, kTransition] at hmem; simp [hN] at hmem
  | succ e ih =>
      intro seen head hd hreach hpre
      have hhn : head.val < n := by omega
      have hrn : decide (head.val = n) = false := decide_eq_false (by omega)
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read] at hmem
        rcases hwh : W head with _ | sym
        · -- blank: move right, `seen` unchanged
          simp only [mkCell, hwh, kTransition] at hmem
          rw [if_neg (by simp [hrn])] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          rw [echo_moveHead_right g₀ W head _ (by simp [mkCell, hwh]) hhn] at hrest
          refine ih seen ⟨head.val + 1, by omega⟩ (by show n - (head.val + 1) = e; omega) hrest ?_
          rw [take_succ_filterMap g₀, hpre, hwh]; simp
        · rcases sym with t | N
          · simp [mkCell, hwh, kTransition] at hmem
          · cases seen with
            | true => simp [mkCell, hwh, kTransition] at hmem
            | false =>
                by_cases hN : N = g₀.initial
                · subst hN
                  simp only [mkCell, hwh, kTransition] at hmem
                  rw [if_pos (by simp), if_neg (by simp [hrn])] at hmem
                  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  obtain ⟨rfl, rfl, rfl⟩ := hmem
                  rw [echo_moveHead_right g₀ W head _ (by simp [mkCell, hwh]) hhn] at hrest
                  refine ih true ⟨head.val + 1, by omega⟩ (by show n - (head.val + 1) = e; omega)
                    hrest ?_
                  rw [take_succ_filterMap g₀, hpre, hwh]; simp
                · simp only [mkCell, hwh, kTransition] at hmem; simp [hN] at hmem

/-- **Soundness of the `gotoLeft` + accept-check phase.** If `gotoLeft` (from any head) reaches an
accepting configuration, the work track spells `[S]`. -/
lemma gotoLeft_check_sound {n : ℕ} {cfgacc : DLBA.Cfg (KCell g₀) (KState g₀) n}
    (hacc : cfgacc.state = KState.accept) (W : Fin (n + 1) → KWork g₀) :
    ∀ m : ℕ, ∀ head : Fin (n + 1), head.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.gotoLeft, ⟨fun k => mkCell g₀ k (W k), head⟩⟩ cfgacc →
      formW g₀ W = [symbol.nonterminal g₀.initial] := by
  intro m
  induction m with
  | zero =>
      intro head hm hreach
      have h0 : head.val = 0 := hm
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read, mkCell, kTransition] at hmem
        rw [if_pos (show decide (head.val = 0) = true by simp [h0])] at hmem
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        have htape : (DLBA.BoundedTape.write
            (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
            (some (Sum.inr (decide (head.val = 0), decide (head.val = n), W head)))).moveHead
            DLBA.Dir.stay
            = (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n) := by
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          congr 1
          funext k; rw [Function.update_apply]; by_cases hk : k = head
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
        rw [htape] at hrest
        exact check_sound g₀ hacc W (n - head.val) false head rfl hrest (by simp [h0])
  | succ e ih =>
      intro head hm hreach
      have hpos : 0 < head.val := by omega
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read, mkCell, kTransition] at hmem
        rw [if_neg (show ¬ (decide (head.val = 0) = true) by
          simp only [decide_eq_true_eq]; omega)] at hmem
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        have htape : (DLBA.BoundedTape.write
            (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
            (some (Sum.inr (decide (head.val = 0), decide (head.val = n), W head)))).moveHead
            DLBA.Dir.left
            = (⟨fun k => mkCell g₀ k (W k), ⟨head.val - 1, by omega⟩⟩ :
                DLBA.BoundedTape (KCell g₀) n) := by
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hpos]
          congr 1
          funext k; rw [Function.update_apply]; by_cases hk : k = head
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
        rw [htape] at hrest
        exact ih ⟨head.val - 1, by omega⟩ (by show head.val - 1 = e; omega) hrest

/-- The phase-indexed soundness invariant maintained FORWARD along a run from the initial
configuration. The simulator reduces the working form toward `[S]` by reverse rule applications,
so at every reachable configuration the current form derives (forward) to the target `w·terminal`.
The structure (`cAt`/`mkCell`) flows forward from init, which is why the induction is forward. -/
def SoundClaim {n : ℕ} (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]
    (input : Fin (n + 1) → T) (cfg : DLBA.Cfg (KCell g₀) (KState g₀) n) : Prop :=
  (cfg.state = KState.init0 ∧ cfg.tape.contents = cAt g₀ input 0 ∧ cfg.tape.head.val = 0) ∨
  (cfg.state = KState.initSweep ∧ ∃ i : ℕ, cfg.tape.contents = cAt g₀ input i ∧ 1 ≤ i ∧
    (cfg.tape.head.val = i ∧ i ≤ n ∨ cfg.tape.head.val = n ∧ i = n + 1)) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.sim ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.gotoLeft ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ (W : Fin (n + 1) → KWork g₀) (seen : Bool), cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.check seen ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k))) ∧
    ((List.ofFn W).take cfg.tape.head.val).filterMap id
      = (if seen then [symbol.nonterminal g₀.initial] else [])) ∨
  (∃ (W W₀ : Fin (n + 1) → KWork g₀) (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1))
      (Aorig : List (symbol T g₀.nt)),
    cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧ cfg.state = KState.applyRule ri k ∧
    k.val ≤ (g₀.rules[ri]).output_string.length ∧
    (patList g₀ g₀.rules[ri]).length ≤ (g₀.rules[ri]).output_string.length ∧
    (∀ p : Fin (n + 1), cfg.tape.head.val ≤ p.val → W p = W₀ p) ∧
    ((List.ofFn W).take cfg.tape.head.val).filterMap id
      = Aorig ++ (patList g₀ g₀.rules[ri]).take k.val ∧
    ((List.ofFn W₀).take cfg.tape.head.val).filterMap id
      = Aorig ++ (g₀.rules[ri]).output_string.take k.val ∧
    grammar_derives g₀ (formW g₀ W₀) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.accept ∧ formW g₀ W = [symbol.nonterminal g₀.initial] ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k))))

/-- **Forward soundness invariant.** Every configuration reachable from the initial one satisfies
`SoundClaim`. -/
lemma sound_invariant {n : ℕ} (hnc : grammar_noncontracting g₀) (input : Fin (n + 1) → T)
    (cfg : DLBA.Cfg (KCell g₀) (KState g₀) n)
    (hreach : LBA.Reaches (kMachine g₀)
      ⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, n.succ_pos⟩⟩⟩ cfg) :
    SoundClaim g₀ input cfg := by
  induction hreach with
  | refl => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨q', sym, dir, hmem, rfl⟩ := hbc
      simp only [kMachine] at hmem
      rcases ih with ⟨hst, hc0, hh0⟩ | ⟨hst, i, hci, hi1, hcase⟩ |
        ⟨W, hcW, hst, hder⟩ | ⟨W, hcW, hst, hder⟩ | ⟨W, seen, hcW, hst, hder, hacm⟩ |
        ⟨W, W₀, ri, k, Aorig, hcW, hst, hk, hpat, hagree, htkW, htkW₀, hder⟩ |
        ⟨W, hcW, hst, hform, hder⟩
      · -- b = init0
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hc0, cAt, Nat.not_lt_zero, if_false, kTransition,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        refine Or.inr (Or.inl ⟨rfl, 1, ?_, le_refl 1, ?_⟩)
        · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hc0]
          rw [show (some (Sum.inr (true, false, some (symbol.terminal (input b.tape.head))))
                  : KCell g₀) = tmpCell g₀ input b.tape.head from by simp [tmpCell, hh0],
            show cAt g₀ input 0 = cAt g₀ input b.tape.head.val from by rw [hh0], cAt_update, hh0]
        · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          split_ifs with hn0
          · left; exact ⟨by simp [hh0], by omega⟩
          · right; exact ⟨by omega, by omega⟩
      · -- b = initSweep
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hci] at hmem
        rcases hcase with ⟨hhi, hin⟩ | ⟨hhn, hin1⟩
        · -- convert cell `i` (raw), move right
          have hcell : cAt g₀ input i b.tape.head = some (Sum.inl (input b.tape.head)) := by
            simp only [cAt, if_neg (show ¬ b.tape.head.val < i by omega)]
          rw [hcell, kTransition] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inl ⟨rfl, i + 1, ?_, by omega, ?_⟩)
          · funext k
            simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hci,
              Function.update_apply]
            by_cases hk : k = b.tape.head
            · subst hk; rw [if_pos rfl]
              simp only [cAt, if_pos (show b.tape.head.val < i + 1 by omega), tmpCell,
                decide_eq_false (show ¬ b.tape.head.val = 0 by omega)]
            · rw [if_neg hk]
              have hki : k.val ≠ i := fun h => hk (Fin.ext (by rw [h, hhi]))
              simp only [cAt]
              by_cases h1 : k.val < i
              · rw [if_pos h1, if_pos (show k.val < i + 1 by omega)]
              · rw [if_neg h1, if_neg (show ¬ k.val < i + 1 by omega)]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            split_ifs with hn0
            · left; exact ⟨by simp [hhi], by omega⟩
            · right; exact ⟨by omega, by omega⟩
        · -- clamp at the right end (cell already converted): enter `sim`
          have hcell : cAt g₀ input i b.tape.head
              = some (Sum.inr (decide (b.tape.head.val = 0), false,
                  some (symbol.terminal (input b.tape.head)))) := by
            simp only [cAt, if_pos (show b.tape.head.val < i by omega), tmpCell]
          rw [hcell, kTransition] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inl
            ⟨fun k => some (symbol.terminal (input k)), ?_, rfl, ?_⟩))
          · funext k
            simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hci, Function.update_apply]
            by_cases hk : k = b.tape.head
            · subst hk; rw [if_pos rfl]; simp [mkCell, hhn]
            · rw [if_neg hk]
              have hkn : k.val ≠ n := fun h => hk (Fin.ext (h.trans hhn.symm))
              simp only [cAt, if_pos (show k.val < i by omega), tmpCell, mkCell,
                decide_eq_false hkn]
          · rw [formW_of_forall_some g₀ _ (fun k => symbol.terminal (input k)) (fun _ => rfl)]
            exact Relation.ReflTransGen.refl
      · -- b = sim
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        have hcon : ∀ (d : DLBA.Dir),
            ((DLBA.BoundedTape.write b.tape
                (mkCell g₀ b.tape.head (W b.tape.head))).moveHead d).contents
              = fun k => mkCell g₀ k (W k) := by
          intro d
          cases d <;>
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
            funext k; rw [Function.update_apply]; by_cases hk : k = b.tape.head
            · subst hk; simp [mkCell]
            · rw [if_neg hk]
        simp only [mkCell, kTransition, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Set.mem_setOf_eq] at hmem
        rcases hmem with (h | h | h) | ⟨ri, h⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩)))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          have hpatlen : (patList g₀ g₀.rules[ri]).length
              ≤ (g₀.rules[ri]).output_string.length := by
            have h1 := hnc (g₀.rules[ri]) (List.getElem_mem _)
            simp only [patList, List.length_append, List.length_cons, List.length_nil]
            omega
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨W, W, ri, 0, ((List.ofFn W).take b.tape.head.val).filterMap id,
              hcon _, rfl, Nat.zero_le _, hpatlen, fun p _ => rfl, ?_, ?_, hder⟩)))))
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Fin.val_zero,
              List.take_zero, List.filterMap_nil, List.append_nil]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Fin.val_zero,
              List.take_zero, List.filterMap_nil, List.append_nil]
      · -- b = gotoLeft
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        set h := b.tape.head with hh
        by_cases hh0 : h.val = 0
        · -- at the left end: enter the check sweep
          simp only [mkCell, kTransition] at hmem
          rw [if_pos (show decide (h.val = 0) = true by simp [hh0])] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, false, ?_, rfl, hder, ?_⟩))))
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
            funext k; rw [Function.update_apply]; by_cases hk : k = h
            · subst hk; simp [mkCell]
            · rw [if_neg hk]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            rw [show b.tape.head.val = 0 from hh0]; simp
        · -- move left, stay in gotoLeft
          simp only [mkCell, kTransition] at hmem
          rw [if_neg (show ¬ (decide (h.val = 0) = true) by
            simp only [decide_eq_true_eq]; exact hh0)] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨W, ?_, rfl, hder⟩)))
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
          funext k; rw [Function.update_apply]; by_cases hk : k = h
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
      · -- b = check seen
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        have hcon : ∀ (x : KWork g₀),
            mkCell g₀ b.tape.head x = mkCell g₀ b.tape.head (W b.tape.head) →
            (DLBA.BoundedTape.write b.tape (mkCell g₀ b.tape.head x)).contents
              = fun k => mkCell g₀ k (W k) := by
          intro x hx
          simp only [DLBA.BoundedTape.write, hcW]
          funext k; rw [Function.update_apply]; by_cases hk : k = b.tape.head
          · subst hk; rw [if_pos rfl]; exact hx
          · rw [if_neg hk]
        have hdrop_nil : ∀ (_ : b.tape.head.val = n),
            ((List.ofFn W).drop (b.tape.head.val + 1)).filterMap id = [] := fun hrn => by
          rw [List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.filterMap_nil]
        rcases hwh : W b.tape.head with _ | symb
        · -- blank cell
          by_cases hrn : b.tape.head.val = n
          · cases seen with
            | false =>
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp at hmem
            | true =>
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp only [if_true, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨W, ?_, rfl, ?_, hder⟩)))))
                · simp only [DLBA.BoundedTape.moveHead]
                  exact hcon none (by rw [hwh])
                · rw [decodeForm_split_head g₀ W b.tape.head _ hacm, hdrop_nil hrn, hwh]; simp
          · -- h < n: move right, keep seen
            have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
            simp only [mkCell, hwh, kTransition] at hmem
            rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
              simp only [decide_eq_true_eq]; omega)] at hmem
            simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl, rfl⟩ := hmem
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, seen, ?_, rfl, hder, ?_⟩))))
            · simp only [DLBA.BoundedTape.moveHead, dif_pos hlt]
              exact hcon none (by rw [hwh])
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
              rw [dif_pos (show b.tape.head.val < n from hlt)]
              show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W b.tape.head, hacm, hwh]; simp
        · rcases symb with t | N
          · -- terminal: stuck
            simp [mkCell, hwh, kTransition] at hmem
          · -- nonterminal N
            by_cases hN : N = g₀.initial ∧ seen = false
            · obtain ⟨rfl, hsf⟩ := hN
              by_cases hrn : b.tape.head.val = n
              · simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show True ∧ ¬ (seen = true) from ⟨trivial, by simp [hsf]⟩),
                  if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨W, ?_, rfl, ?_, hder⟩)))))
                · simp only [DLBA.BoundedTape.moveHead]
                  exact hcon _ (by rw [hwh])
                · rw [decodeForm_split_head g₀ W b.tape.head _ hacm, hdrop_nil hrn, hwh, hsf]; simp
              · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show True ∧ ¬ (seen = true) from ⟨trivial, by simp [hsf]⟩),
                  if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
                    simp only [decide_eq_true_eq]; omega)] at hmem
                simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, true, ?_, rfl, hder, ?_⟩))))
                · simp only [DLBA.BoundedTape.moveHead, dif_pos hlt]
                  exact hcon _ (by rw [hwh])
                · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
                  rw [dif_pos (show b.tape.head.val < n from hlt)]
                  show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
                  rw [take_succ_filterMap g₀ W b.tape.head, hacm, hsf, hwh]; simp
            · -- condition fails: stuck
              rw [not_and_or] at hN
              simp only [mkCell, hwh, kTransition] at hmem
              rcases hN with hN | hN
              · rw [if_neg (by tauto)] at hmem; simp at hmem
              · simp only [Bool.not_eq_false] at hN
                rw [if_neg (by simp [hN])] at hmem; simp at hmem
      · -- b = applyRule ri k
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        rcases hwh : W b.tape.head with _ | s
        · -- blank: skip (move right), same `k`
          by_cases hrn : b.tape.head.val = n
          · simp only [mkCell, hwh, kTransition] at hmem
            rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
            simp at hmem
          · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
            simp only [mkCell, hwh, kTransition] at hmem
            rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
              simp only [decide_eq_true_eq]; omega)] at hmem
            simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl, rfl⟩ := hmem
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨W, W₀, ri, k, Aorig, ?_, rfl, hk, hpat, ?_, ?_, ?_, hder⟩)))))
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt, hcW]
              funext p; rw [Function.update_apply]; by_cases hp : p = b.tape.head
              · subst hp; simp [mkCell, hwh]
              · rw [if_neg hp]
            · intro p hp
              simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt] at hp
              exact hagree p (by omega)
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
              show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W b.tape.head, htkW, hwh]; simp
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
              show ((List.ofFn W₀).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀,
                show W₀ b.tape.head = none from by
                  rw [← hagree b.tape.head (le_refl _)]; exact hwh]
              simp
        · -- symbol `s`: match `output[k]` and write the replacement
          simp only [mkCell, hwh, kTransition] at hmem
          by_cases hm : (g₀.rules[ri]).output_string[k.val]? = some s
          swap
          · rw [if_neg hm] at hmem; simp at hmem
          rw [if_pos hm] at hmem
          have hklt : k.val < (g₀.rules[ri]).output_string.length :=
            List.getElem?_eq_some_iff.mp hm |>.1
          have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 := by
            apply Fin.val_add_one_of_lt'
            have := output_length_le_ruleBound g₀ ri; omega
          have hW₀h : W₀ b.tape.head = some s := (hagree b.tape.head (le_refl _)).symm.trans hwh
          have peel : ∀ (l : List (symbol T g₀.nt)) (m : ℕ),
              l.take m ++ ([l[m]?].filterMap id) = l.take (m + 1) := by
            intro l m
            rcases lt_or_ge m l.length with hm' | hm'
            · simp only [List.getElem?_eq_getElem hm', List.filterMap_cons, id, List.filterMap_nil]
              exact List.take_concat_get' _ _ hm'
            · rw [List.getElem?_eq_none (by omega)]
              simp only [List.filterMap_cons, id, List.filterMap_nil, List.append_nil]
              rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          -- `take head` of the updated tape is unchanged (the write is at `head`).
          have htkW'eq : ((List.ofFn (Function.update W b.tape.head
                ((patList g₀ g₀.rules[ri])[k.val]?))).take b.tape.head.val).filterMap id
              = Aorig ++ (patList g₀ g₀.rules[ri]).take k.val := by
            rw [show (List.ofFn (Function.update W b.tape.head
                  ((patList g₀ g₀.rules[ri])[k.val]?))).take b.tape.head.val
                = (List.ofFn W).take b.tape.head.val from by
              apply List.ext_getElem (by simp)
              intro j hj1 _
              have hjlt : j < b.tape.head.val := by
                rw [List.length_take, List.length_ofFn] at hj1; omega
              simp only [List.getElem_take, ofFn_update, List.getElem_ofFn,
                List.getElem_set_ne (show b.tape.head.val ≠ j from by omega)]]
            exact htkW
          by_cases hk1 : k.val + 1 < (g₀.rules[ri]).output_string.length
          · -- continue
            rw [if_pos hk1] at hmem
            by_cases hrn : b.tape.head.val = n
            · rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
              simp at hmem
            · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
              rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
                simp only [decide_eq_true_eq]; omega)] at hmem
              simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              obtain ⟨rfl, rfl, rfl⟩ := hmem
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨Function.update W b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?), W₀, ri, k + 1,
                  Aorig, ?_, rfl, ?_, hpat, ?_, ?_, ?_, hder⟩)))))
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt, hcW]
                rw [show (some (Sum.inr (decide (b.tape.head.val = 0), decide (b.tape.head.val = n),
                      (patList g₀ g₀.rules[ri])[k.val]?)) : KCell g₀)
                    = mkCell g₀ b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?) from rfl,
                  update_mkCell]
              · rw [hval]; omega
              · intro p hp
                simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt] at hp
                rw [Function.update_of_ne (fun he => by rw [he] at hp; omega)]
                exact hagree p (by omega)
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
                show ((List.ofFn (Function.update W b.tape.head _)).take
                  (b.tape.head.val + 1)).filterMap id = _
                rw [take_succ_filterMap g₀ _ b.tape.head, Function.update_self, htkW'eq, hval,
                  List.append_assoc, peel]
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
                show ((List.ofFn W₀).take (b.tape.head.val + 1)).filterMap id = _
                rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀, hW₀h, hval, List.append_assoc]
                congr 1
                rw [show ([some s].filterMap id) = ([(g₀.rules[ri]).output_string[k.val]?].filterMap id)
                    from by rw [hm], peel]
          · by_cases hk2 : k.val + 1 = (g₀.rules[ri]).output_string.length
            · -- last symbol: return to `sim`
              rw [if_neg hk1, if_pos hk2] at hmem
              simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              obtain ⟨rfl, rfl, rfl⟩ := hmem
              refine Or.inr (Or.inr (Or.inl
                ⟨Function.update W b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?), ?_, rfl, ?_⟩))
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
                rw [show (some (Sum.inr (decide (b.tape.head.val = 0), decide (b.tape.head.val = n),
                      (patList g₀ g₀.rules[ri])[k.val]?)) : KCell g₀)
                    = mkCell g₀ b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?) from rfl, update_mkCell]
              · have hB : ((List.ofFn (Function.update W b.tape.head
                      ((patList g₀ g₀.rules[ri])[k.val]?))).drop (b.tape.head.val + 1)).filterMap id
                    = ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  congr 1
                  apply List.ext_getElem (by simp)
                  intro j hj1 _
                  have hjb : b.tape.head.val + 1 + j < n + 1 := by
                    rw [List.length_drop, List.length_ofFn] at hj1; omega
                  rw [List.getElem_drop, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn,
                    Function.update_of_ne (show (⟨b.tape.head.val + 1 + j, hjb⟩ : Fin (n + 1))
                      ≠ b.tape.head from by rw [ne_eq, Fin.ext_iff]; simp only []; omega)]
                  exact hagree _ (by simp only []; omega)
                have hfW' : formW g₀ (Function.update W b.tape.head
                      ((patList g₀ g₀.rules[ri])[k.val]?))
                    = Aorig ++ patList g₀ g₀.rules[ri]
                      ++ ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  rw [formW_split g₀ _ (b.tape.head.val + 1), hB]
                  congr 1
                  rw [take_succ_filterMap g₀ _ b.tape.head, Function.update_self, htkW'eq,
                    List.append_assoc, peel, List.take_of_length_le (by omega)]
                have hfW₀ : formW g₀ W₀ = Aorig ++ (g₀.rules[ri]).output_string
                    ++ ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  rw [formW_split g₀ W₀ (b.tape.head.val + 1)]
                  congr 1
                  rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀, hW₀h, List.append_assoc]
                  congr 1
                  rw [show ([some s].filterMap id)
                      = ([(g₀.rules[ri]).output_string[k.val]?].filterMap id) from by rw [hm], peel,
                    List.take_of_length_le (by omega)]
                rw [hfW']
                exact Relation.ReflTransGen.head
                  (grammar_transforms_patList g₀ (List.getElem_mem _) Aorig _) (hfW₀ ▸ hder)
            · rw [if_neg hk1, if_neg hk2] at hmem; simp at hmem
      · -- b = accept: no successor
        rw [hst] at hmem; simp [kTransition] at hmem

end Sound

/-- **Soundness of the simulator.** If the backward simulator accepts `w`, then the working
track passed through a valid (reverse) derivation, so `g₀` derives `w` from its start symbol. -/
theorem kMachine_sound [Fintype T] [DecidableEq T] (g₀ : grammar T)
    [Fintype g₀.nt] [DecidableEq g₀.nt] (hnc : grammar_noncontracting g₀) (w : List T) :
    LBA.LanguageViaEmbed (kMachine g₀) (fun t => some (Sum.inl t)) w → grammar_language g₀ w := by
  rintro ⟨hne, hAcc⟩
  set L := List.map (fun t => (some (Sum.inl t) : KCell g₀)) w with hL
  have hLlen : L.length = w.length := by rw [hL, List.length_map]
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hne
  set n := L.length - 1 with hn
  have hn1 : n + 1 = w.length := by omega
  have hbound : ∀ i : Fin (n + 1), i.val < w.length := fun i => by have := i.isLt; omega
  set input : Fin (n + 1) → T := fun i => w.get ⟨i.val, hbound i⟩ with hinput
  have htape : (LBA.loadList L hne).contents = cAt g₀ input 0 := by
    funext i
    simp only [LBA.loadList, cAt, Nat.not_lt_zero, if_false, hinput, hL,
      List.get_eq_getElem, List.getElem_map]
  have hbridge : LBA.initCfgList (kMachine g₀) L hne
      = (⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (KCell g₀) (KState g₀) n) := by
    refine cfg_eq g₀ rfl htape (Fin.ext ?_)
    simp [LBA.loadList]
  obtain ⟨cfgacc, hreach, hacc⟩ := hAcc
  rw [hbridge] at hreach
  have hSC := sound_invariant g₀ hnc input cfgacc hreach
  have hst : cfgacc.state = KState.accept := by simpa [kMachine] using hacc
  have htgt : List.ofFn (fun k => (symbol.terminal (input k) : symbol T g₀.nt))
      = List.map symbol.terminal w := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map]; omega
    · intro j h1 _
      simp only [List.getElem_ofFn, List.getElem_map, hinput, List.get_eq_getElem]
  rcases hSC with ⟨h2, _, _⟩ | ⟨h2, _⟩ | ⟨_, _, h2, _⟩ | ⟨_, _, h2, _⟩ | ⟨_, _, _, h2, _, _⟩ |
    ⟨_, _, _, _, _, _, h2, _, _, _, _, _, _⟩ | ⟨W, _, _, hform, hder⟩
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · rw [hform, htgt] at hder; exact hder

/-- **Completeness of the simulator.** A derivation `[S] ⇒* w` is replayed in reverse on the
tape (convert input, repeatedly bubble blanks and apply rules backward, then verify `[S]`),
yielding an accepting run. Non-contraction keeps every sentential form within `|w|` cells. -/
theorem kMachine_complete [Fintype T] [DecidableEq T] (g₀ : grammar T)
    [Fintype g₀.nt] [DecidableEq g₀.nt] (hnc : grammar_noncontracting g₀) (w : List T) :
    grammar_language g₀ w → LBA.LanguageViaEmbed (kMachine g₀) (fun t => some (Sum.inl t)) w := by
  intro hw
  -- `hw : grammar_derives g₀ [S] (w.map terminal)`.
  -- Non-contraction forbids deriving the empty word, so `w ≠ []`.
  have htrlen : ∀ {a b : List (symbol T g₀.nt)}, grammar_transforms g₀ a b → a.length ≤ b.length := by
    rintro a b ⟨r, hr, u, v, rfl, rfl⟩
    have := hnc r hr
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hderlen : ∀ {a b : List (symbol T g₀.nt)}, grammar_derives g₀ a b → a.length ≤ b.length := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | tail _ h₂ ih => exact le_trans ih (htrlen h₂)
  have hwne : w ≠ [] := by
    intro h0; have hl := hderlen hw; rw [h0] at hl; simp at hl
  have hmapne : List.map (fun t => some (Sum.inl t)) w ≠ ([] : List (KCell g₀)) := by
    simpa using hwne
  refine ⟨hmapne, ?_⟩
  set L := List.map (fun t => some (Sum.inl t)) w with hL
  have hLlen : L.length = w.length := by rw [hL, List.length_map]
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hmapne
  set n := L.length - 1 with hn
  have hn1 : n + 1 = w.length := by omega
  have hbound : ∀ i : Fin (n + 1), i.val < w.length := fun i => by have := i.isLt; omega
  set input : Fin (n + 1) → T := fun i => w.get ⟨i.val, hbound i⟩ with hinput
  -- The initial configuration is the raw input tape (`cAt input 0`) at the left end.
  have htape : (LBA.loadList L hmapne).contents = cAt g₀ input 0 := by
    funext i
    simp only [LBA.loadList, cAt, Nat.not_lt_zero, if_false, hinput, hL,
      List.get_eq_getElem, List.getElem_map]
  -- After the init sweep the work track holds `terminal (input k)` in every cell.
  obtain ⟨h0, hinit⟩ := init_reaches g₀ input
  set W₀ : Fin (n + 1) → KWork g₀ := fun k => some (symbol.terminal (input k)) with hW₀
  have hform0 : formW g₀ W₀ = List.map symbol.terminal w := by
    rw [formW_of_forall_some g₀ W₀ (fun k => symbol.terminal (input k)) (fun _ => rfl)]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map]; omega
    · intro j h1 _
      simp only [List.getElem_ofFn, List.getElem_map, hinput, List.get_eq_getElem]
  -- Replay the derivation backwards down to `[S]`.
  obtain ⟨W', h', hderiv, hformS⟩ := derive_back g₀ hnc hw W₀ h0 hform0
  obtain ⟨j, hj, hother⟩ :=
    filterMap_ofFn_singleton W' (symbol.nonterminal g₀.initial) hformS
  -- The accept check then succeeds.
  obtain ⟨cfg_acc, hreach_acc, hacc_state⟩ := accept_from_S g₀ W' j hj hother h'
  refine ⟨cfg_acc, ?_, hacc_state⟩
  -- Stitch: init config = `⟨init0, cAt input 0, 0⟩`, then init ⟶ sim ⟶ [S] ⟶ accept.
  have hbridge : LBA.initCfgList (kMachine g₀) L hmapne
      = (⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (KCell g₀) (KState g₀) n) := by
    refine cfg_eq g₀ rfl htape (Fin.ext ?_)
    simp [LBA.loadList]
  rw [hbridge]
  exact (hinit.trans hderiv).trans hreach_acc

/-- **Kuroda's construction (core).** A non-contracting grammar with finitely many
nonterminals is simulated by a nondeterministic LBA: on a tape of `|w|` cells (alphabet
`Option (T ⊕ Γ)` for a finite work alphabet `Γ`), the automaton nondeterministically replays a
derivation of the grammar on a working track and accepts iff that track ends up equal to the
input word. Non-contraction bounds every sentential form by `|w|`, so the tape never overflows.

This isolates the entire machine construction and its two-way simulation correctness; the
empty-word bookkeeping and the reduction from an arbitrary context-sensitive grammar are done
in `Equivalence/ContextSensitive.lean`. -/
theorem noncontracting_finite_to_LBA [Fintype T] [DecidableEq T]
    (g₀ : grammar T) (hfin : Finite g₀.nt) (hnc : grammar_noncontracting g₀) :
    ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
      (_ : DecidableEq Γ) (_ : DecidableEq Λ)
      (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
      LBA.LanguageViaEmbed M (fun t => some (Sum.inl t)) = grammar_language g₀ := by
  haveI : Fintype g₀.nt := Fintype.ofFinite _
  haveI : DecidableEq g₀.nt := Classical.decEq _
  refine ⟨KGamma g₀, KState g₀, inferInstance, inferInstance, inferInstance, inferInstance,
    kMachine g₀, ?_⟩
  funext w
  apply propext
  constructor
  · -- soundness: an accepting run on `w` exhibits a derivation `[S] ⇒* w`
    exact kMachine_sound g₀ hnc w
  · -- completeness: a derivation `[S] ⇒* w` is replayed by an accepting run
    exact kMachine_complete g₀ hnc w

end

end KurodaConstruction
