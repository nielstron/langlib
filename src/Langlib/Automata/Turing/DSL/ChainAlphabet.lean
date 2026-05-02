import Mathlib
import Langlib.Automata.Turing.DSL.ParrecChain

/-! # Chain Alphabet — Binary Representation on ChainΓ

This file provides basic definitions and lemmas for working with the
chain tape alphabet `ChainΓ`:

- `γ'ToChainΓ` and `chainConsBottom`: distinguished cells
- `chainBinaryRepr`: binary representation of natural numbers as ChainΓ cells
- `decodeBinaryBlock`: decoding ChainΓ cells back to natural numbers
- Basic properties: non-defaultness, absence of separators, encode/decode roundtrip
-/

open Turing PartrecToTM2 TM2to1

/-! ### Instances -/

noncomputable instance instDecEqChainΓ' : DecidableEq ChainΓ :=
  instDecidableEqProd (α := Bool) (β := (K' → Option Γ'))

/-! ### Distinguished ChainΓ cells -/

/-- Map a Γ' value to its corresponding ChainΓ cell (without bottom marker). -/
noncomputable def γ'ToChainΓ (γ' : Γ') : ChainΓ :=
  (false, Function.update (fun _ => none) K'.main (some γ'))

/-- The ChainΓ cell for the bottom marker with cons. -/
noncomputable def chainConsBottom : ChainΓ :=
  (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- `chainConsBottom` is non-default. -/
theorem chainConsBottom_ne_default : chainConsBottom ≠ (default : ChainΓ) := by
  simp +decide [chainConsBottom]

/-! ### Binary Representation -/

/-- Binary representation of n as ChainΓ cells (LSB first, no markers). -/
noncomputable def chainBinaryRepr (n : ℕ) : List ChainΓ :=
  (trNat n).map γ'ToChainΓ

/-- `chainBinaryRepr 0` is the empty list. -/
theorem chainBinaryRepr_zero : chainBinaryRepr 0 = [] := by
  simp +decide [chainBinaryRepr, trNat]

/-- All elements of `chainBinaryRepr n` are non-default. -/
theorem chainBinaryRepr_ne_default (n : ℕ) :
    ∀ g ∈ chainBinaryRepr n, g ≠ (default : ChainΓ) := by
  intro g hg
  obtain ⟨ γ', _, rfl ⟩ := List.mem_map.mp hg
  cases γ' <;> simp +decide [γ'ToChainΓ]

/-- `chainBinaryRepr n` never contains `chainConsBottom`.
    Binary cells have `Bool` component `false`, while `chainConsBottom`
    has `Bool` component `true`. -/
theorem chainBinaryRepr_no_consBottom (n : ℕ) :
    ∀ c ∈ chainBinaryRepr n, c ≠ chainConsBottom := by
  unfold chainBinaryRepr chainConsBottom;
  unfold γ'ToChainΓ; simp +decide ;
  grind

/-! ### Chain Encoding Decomposition Equation -/

/-- `trInit K'.main (trList [n])` decomposes as
    `[chainConsBottom] ++ (chainBinaryRepr n).reverse`. -/
theorem trInit_trList_singleton_eq (n : ℕ) :
    @trInit K' (fun _ => Γ') _ K'.main (trList [n]) =
    chainConsBottom :: (chainBinaryRepr n).reverse := by
  unfold trList; simp +decide [ chainBinaryRepr ] ;
  unfold trInit; simp +decide [ chainConsBottom ] ;
  unfold γ'ToChainΓ; aesop;

/-! ### Binary Representation Helpers -/

theorem num_cast_ne_zero (n : ℕ) (hn : n ≠ 0) : (n : Num) ≠ 0 := by
  intro h; apply hn
  have := congr_arg (· : Num → ℕ) h
  simp at this; exact this

theorem chainBinaryRepr_double (n : ℕ) (hn : n ≠ 0) :
    chainBinaryRepr (2 * n) = γ'ToChainΓ Γ'.bit0 :: chainBinaryRepr n := by
  simp only [chainBinaryRepr, trNat]
  have h_eq : (↑(2 * n) : Num) = ((↑n : Num)).bit0 := by
    have : 2 * n = Nat.bit false n := by simp [Nat.bit]
    rw [this]; show Num.ofNat' _ = _; rw [Num.ofNat'_bit]; simp
  rw [h_eq]
  cases hc : (↑n : Num) with
  | zero => exact absurd hc (num_cast_ne_zero n hn)
  | pos p => simp [Num.bit0, trNum, trPosNum]

theorem chainBinaryRepr_double_succ (n : ℕ) :
    chainBinaryRepr (2 * n + 1) = γ'ToChainΓ Γ'.bit1 :: chainBinaryRepr n := by
  simp only [chainBinaryRepr, trNat]
  have h_eq : (↑(2 * n + 1) : Num) = ((↑n : Num)).bit1 := by
    have : 2 * n + 1 = Nat.bit true n := by simp [Nat.bit]
    rw [this]; show Num.ofNat' _ = _; rw [Num.ofNat'_bit]; simp
  rw [h_eq]
  cases hc : (↑n : Num) with
  | zero => simp [Num.bit1, trNum, trPosNum]
  | pos p => simp [Num.bit1, trNum, trPosNum]

theorem chainBinaryRepr_eq_nil_iff (n : ℕ) :
    chainBinaryRepr n = [] ↔ n = 0 := by
  constructor
  · intro h; simp [chainBinaryRepr, trNat] at h
    by_contra hn; push_neg at hn
    cases hc : (↑n : Num) with
    | zero => have := congr_arg (· : Num → ℕ) hc; simp at this; exact hn this
    | pos p => rw [hc] at h; simp [trNum] at h; cases p <;> simp [trPosNum] at h
  · intro h; subst h; simp +decide [chainBinaryRepr, trNat]

/-! ### Decoding binary blocks -/

/-- Decode a list of ChainΓ cells back to a natural number.
    This is the left inverse of `chainBinaryRepr` on valid inputs. -/
noncomputable def decodeBinaryBlock : List ChainΓ → ℕ
  | [] => 0
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then
      2 * decodeBinaryBlock rest
    else if c = γ'ToChainΓ Γ'.bit1 then
      2 * decodeBinaryBlock rest + 1
    else
      0

/-- `decodeBinaryBlock` is a left inverse of `chainBinaryRepr`. -/
@[simp]
theorem decodeBinaryBlock_chainBinaryRepr (n : ℕ) :
    decodeBinaryBlock (chainBinaryRepr n) = n := by
  have h_decode_even : ∀ n, decodeBinaryBlock (chainBinaryRepr (2 * n)) = 2 * decodeBinaryBlock (chainBinaryRepr n) := by
    intro n
    simp [chainBinaryRepr, trNat];
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.mul_succ ];
    erw [ show ( 2 * ( n + 1 ) : Num ) = Num.bit0 ( n + 1 ) from ?_ ];
    · cases h : ( n + 1 : Num ) ; simp_all +decide [ trNum ];
      aesop;
    · norm_cast;
      grind +suggestions;
  have h_decode_odd : ∀ n, decodeBinaryBlock (chainBinaryRepr (2 * n + 1)) = 2 * decodeBinaryBlock (chainBinaryRepr n) + 1 := by
    intro n;
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.mul_succ, chainBinaryRepr ];
    unfold trNat; simp +decide [ Nat.mul_succ, chainBinaryRepr ] ;
    erw [ show ( 2 * n + 2 + 1 : Num ) = Num.bit1 ( n + 1 ) by
            grind +suggestions ];
    cases h : ( n : Num ) + 1 <;> simp_all +decide [ Num.bit1 ];
    cases ‹PosNum› <;> rfl;
  induction' n using Nat.strong_induction_on with n ih; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
  cases k <;> simp_all +arith +decide
