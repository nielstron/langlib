module

public import Langlib.Automata.LinearBounded.Definition
public import Langlib.Grammars.Unrestricted.Definition
public import Langlib.Grammars.NonContracting.Definition
import Mathlib.Tactic
@[expose]
public section

/-!
# CSG → LBA (Kuroda): the simulating machine and its single-step semantics

This file builds the backward-simulating LBA `kMachine g₀` for a non-contracting grammar `g₀`
with finitely many nonterminals, and develops all the shared infrastructure used by both
halves of the language equality:

* the work alphabet (`KWork`/`KGamma`/`KCell`), states (`KState`), transition (`kTransition`)
  and machine (`kMachine`);
* decoding the work track to a sentential form (`formW`, `formOf`) and its list lemmas;
* the single-step "echo" glue (`kStep_echo_*`), the marked-tape sweeps (`gotoLeft_reaches`,
  `check_sweep`, `accept_from_S`) and the canonical cell `mkCell`;
* the initial conversion sweep (`cAt`, `init_reaches`).

The completeness and soundness arguments live in `CSGToLBA/Completeness.lean` and
`CSGToLBA/Soundness.lean`.

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
end

end KurodaConstruction
