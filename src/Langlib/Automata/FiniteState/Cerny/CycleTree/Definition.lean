module

public import Langlib.Automata.FiniteState.Synchronizing

@[expose]
public section

/-!
# The three-arm cycle-tree automata

This module gives the hidden-cycle coordinate presentation used by the
cycle-tree analysis.  Words act on the right because Mathlib's
`DFA.evalFrom` is a left fold.
-/

namespace DFA.CycleTree

/-- The two generators of a cycle-tree automaton. -/
inductive Letter
  | p
  | s
  deriving DecidableEq, Fintype, Repr

/-- The three nonnegative arm parameters. -/
structure Params where
  X : ℕ
  R : ℕ
  L : ℕ
  deriving DecidableEq, Repr

namespace Params

def ell (P : Params) : ℕ := 2 * P.X + 2

def m (P : Params) : ℕ := P.X + P.R + 1

def rho (P : Params) : ℕ := 2 * P.m + 1

def cycle (P : Params) : ℕ := 2 * P.R + 2 * P.L + 3

def order (P : Params) : ℕ := P.ell + P.cycle

theorem order_eq (P : Params) :
    P.order = 2 * (P.X + P.R + P.L) + 5 := by
  simp [order, ell, cycle]
  omega

theorem ell_pos (P : Params) : 0 < P.ell := by
  simp [ell]

theorem cycle_pos (P : Params) : 0 < P.cycle := by
  simp [cycle]

theorem order_pos (P : Params) : 0 < P.order := by
  simp [order, ell, cycle]

theorem ell_lt_order (P : Params) : P.ell < P.order := by
  simp [order, cycle]

theorem rho_eq (P : Params) : P.rho = P.ell + 2 * P.R + 1 := by
  simp [rho, m, ell]
  omega

theorem rho_lt_order (P : Params) : P.rho < P.order := by
  rw [rho_eq]
  simp [order, cycle]
  omega

end Params

/-- State coordinates `0, ..., n-1` in hidden-cycle order. -/
abbrev State (P : Params) := Fin P.order

/-- Convert a natural coordinate to a state, reducing modulo the order.

Every branch of `pMap` and `sMap` below already lies in the canonical
interval; using one total constructor keeps the executable definition free
of branch-local proof terms.
-/
def Params.stateOfNat (P : Params) (coordinate : ℕ) : State P :=
  ⟨coordinate % P.order, Nat.mod_lt _ P.order_pos⟩

/-- The permutation generator in hidden-cycle coordinates. -/
def pMap (P : Params) (state : State P) : State P :=
  let x := state.val
  if _h0 : x = 0 then
    P.stateOfNat 1
  else if _h1 : x = 1 then
    P.stateOfNat P.ell
  else if _hEll : x = P.ell then
    P.stateOfNat P.rho
  else if _hRho : x = P.rho then
    P.stateOfNat 0
  else if _hBeforeEll : x < P.ell then
    P.stateOfNat (P.ell + 1 - x)
  else if _hBeforeRho : x < P.rho then
    P.stateOfNat (P.ell + P.rho - x)
  else
    P.stateOfNat (P.rho + P.order - x)

/-- The defect-one generator in hidden-cycle coordinates. -/
def sMap (P : Params) (state : State P) : State P :=
  let x := state.val
  if _h0 : x = 0 then
    P.stateOfNat (P.rho - 1)
  else if _hEll : x = P.ell then
    P.stateOfNat (P.rho - 1)
  else if _hBeforeEll : x < P.ell then
    P.stateOfNat (P.ell - x)
  else if _hBeforeRho : x < P.rho then
    P.stateOfNat (P.ell + P.rho - 1 - x)
  else
    P.stateOfNat (P.rho + P.order - 1 - x)

/-- The cycle-tree automaton as a Langlib/Mathlib DFA.

The arbitrary acceptance set is `univ`; synchronization depends only on
`step`.
-/
def automaton (P : Params) : DFA Letter (State P) where
  step state
    | .p => pMap P state
    | .s => sMap P state
  start := ⟨0, P.order_pos⟩
  accept := Set.univ

/-- Concatenate `count` copies of a word. -/
def wordPow {Alpha : Type*} (word : List Alpha) (count : ℕ) : List Alpha :=
  (List.replicate count word).flatten

@[simp]
theorem wordPow_zero {Alpha : Type*} (word : List Alpha) :
    wordPow word 0 = [] := by
  simp [wordPow]

@[simp]
theorem wordPow_succ {Alpha : Type*} (word : List Alpha) (count : ℕ) :
    wordPow word (count + 1) = word ++ wordPow word count := by
  simp [wordPow, List.replicate_succ]

theorem wordPow_succ_right {Alpha : Type*} (word : List Alpha) (count : ℕ) :
    wordPow word (count + 1) = wordPow word count ++ word := by
  simp [wordPow, List.replicate_succ']

theorem wordPow_add {Alpha : Type*} (word : List Alpha) (left right : ℕ) :
    wordPow word (left + right) =
      wordPow word left ++ wordPow word right := by
  unfold wordPow
  rw [List.replicate_add, List.flatten_append]

theorem wordPow_mul {Alpha : Type*} (word : List Alpha)
    (width count : ℕ) :
    wordPow word (count * width) =
      wordPow (wordPow word width) count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Nat.succ_mul, wordPow_add, ih, wordPow_succ_right]

@[simp]
theorem length_wordPow {Alpha : Type*} (word : List Alpha) (count : ℕ) :
    (wordPow word count).length = count * word.length := by
  simp [wordPow]

def aWord : List Letter := [.s, .p]

def cWord : List Letter := [.p, .s]

def pSquared : List Letter := [.p, .p]

def sSquared : List Letter := [.s, .s]

/-- `D = (sp)^(2m) p²`. -/
def dWord (P : Params) : List Letter :=
  wordPow aWord (2 * P.m) ++ pSquared

/-- A word obtained by repeating the macro `D`. -/
def dPowerWord (P : Params) (count : ℕ) : List Letter :=
  wordPow (dWord P) count

@[simp]
theorem length_aWord : aWord.length = 2 := rfl

@[simp]
theorem length_cWord : cWord.length = 2 := rfl

@[simp]
theorem length_pSquared : pSquared.length = 2 := rfl

@[simp]
theorem length_sSquared : sSquared.length = 2 := rfl

@[simp]
theorem length_dWord (P : Params) :
    (dWord P).length = 4 * P.m + 2 := by
  simp [dWord]
  omega

@[simp]
theorem length_dPowerWord (P : Params) (count : ℕ) :
    (dPowerWord P count).length = count * (4 * P.m + 2) := by
  simp [dPowerWord]

/-- Parameters on the final residual diagonal `R = L + 1`. -/
def residualParams (X L : ℕ) : Params :=
  ⟨X, L + 1, L⟩

/-- The common two-depth prefix used by the six finite certificates. -/
def hTwoWord (X L : ℕ) : List Letter :=
  let P := residualParams X L
  [.s] ++ List.replicate 3 .p ++
    wordPow aWord (P.cycle - P.ell - 1) ++
    [.s] ++ List.replicate 2 .p ++ List.replicate 2 .s

/-- Decode the compact `p`/`s` strings stored by the exact search. -/
def decodeWord (encoded : String) : List Letter :=
  encoded.toList.map fun symbol => if symbol = 'p' then .p else .s

end DFA.CycleTree
