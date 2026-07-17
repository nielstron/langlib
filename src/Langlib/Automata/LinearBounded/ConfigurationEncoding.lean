module

public import Langlib.Automata.DeterministicLinearBounded.Definition
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

@[expose]
public section

/-!
# Same-length configuration encoding

This file records a finite-cardinality obstruction to encoding every configuration of one
bounded-tape model into configurations of another while keeping exactly the same number of
tape cells.

For a tape alphabet `A`, state type `P`, and parameter `n`, `DLBA.Cfg A P n` has

`|P| * |A|^(n + 1) * (n + 1)`

elements. Consequently, an injective same-length encoding is impossible whenever the target's
state-and-tape factor is smaller than the source's. In particular, after fixing a target tape
alphabet and state type, some larger finite tape alphabet cannot be encoded injectively at every
cell count without using additional cells.

These are information-capacity statements about static configurations. They do **not** separate
deterministic from nondeterministic LBA languages, and they do not rule out simulations that use
a sufficiently large machine-dependent constant-factor tape expansion.  The final results make
the remaining uniformity obstruction precise: after fixing one target alphabet, state set,
positive expansion factor, and additive cell allowance, a sufficiently large source alphabet
still cannot be encoded injectively at every tape length.
-/

namespace DLBA

variable {A B P Q : Type*} {n : ℕ}
  [Fintype A] [Fintype B] [Fintype P] [Fintype Q]

private theorem eventually_pow_dominates_mul {a b q : ℕ} (hab : b < a) :
    ∃ n : ℕ, q * b ^ (n + 1) < a ^ (n + 1) := by
  by_cases hb0 : b = 0
  · refine ⟨0, ?_⟩
    simp [hb0]
    omega
  · have hb : 0 < b := Nat.pos_of_ne_zero hb0
    let r := q * b
    let d := a - b
    have hd : 1 ≤ d := by omega
    have hbd : b + d = a := by omega
    have hpowpos : 0 < b ^ r := pow_pos hb r
    have hstep : r * b ^ r < (r + 1) * b ^ r :=
      (Nat.mul_lt_mul_right hpowpos).2 (Nat.lt_succ_self r)
    have hscale : (r + 1) * b ^ r ≤ (r + 1) * b ^ r * d := by
      have := Nat.mul_le_mul_left ((r + 1) * b ^ r) hd
      simpa only [mul_one] using this
    have hterm : q * b ^ (r + 1) < (r + 1) * b ^ r * d := by
      rw [pow_succ]
      calc
        q * (b ^ r * b) = r * b ^ r := by
          simp [r, mul_assoc, mul_comm, mul_left_comm]
        _ < (r + 1) * b ^ r := hstep
        _ ≤ (r + 1) * b ^ r * d := hscale
    have hbern :
        b ^ (r + 1) + (r + 1) * b ^ r * d ≤ (b + d) ^ (r + 1) := by
      simpa only [Nat.add_sub_cancel] using
        (pow_add_mul_le_add_pow (R := ℕ) (a := b) (b := d)
          (by omega) (by omega) (r + 1))
    refine ⟨r, ?_⟩
    rw [← hbd]
    exact (hterm.trans_le (Nat.le_add_left _ _)).trans_le hbern

/-- If the source state-and-tape factor is larger than the target factor, no map between their
same-length configuration spaces can be injective. -/
public theorem not_injective_cfg_to_cfg_of_card_lt
    (h :
      Fintype.card Q * Fintype.card B ^ (n + 1) <
        Fintype.card P * Fintype.card A ^ (n + 1))
    (encode : Cfg A P n → Cfg B Q n) :
    ¬ Function.Injective encode := by
  intro hinjective
  have hcard :
      (Fintype.card P * Fintype.card A ^ (n + 1)) * (n + 1) ≤
        (Fintype.card Q * Fintype.card B ^ (n + 1)) * (n + 1) := by
    simpa only [card_cfg] using
      Fintype.card_le_of_injective encode hinjective
  have hstrict :
      (Fintype.card Q * Fintype.card B ^ (n + 1)) * (n + 1) <
        (Fintype.card P * Fintype.card A ^ (n + 1)) * (n + 1) :=
    (Nat.mul_lt_mul_right (Nat.succ_pos n)).2 h
  exact (Nat.not_lt_of_ge hcard) hstrict

/-- A same-length target configuration space cannot injectively hold all source tapes when its
state-and-tape factor is too small. This is the state-free source case of the configuration
counting obstruction. -/
public theorem not_injective_boundedTape_to_cfg_of_card_lt
    (h :
      Fintype.card Q * Fintype.card B ^ (n + 1) <
        Fintype.card A ^ (n + 1))
    (encode : BoundedTape A n → Cfg B Q n) :
    ¬ Function.Injective encode := by
  intro hinjective
  have hcard :
      Fintype.card A ^ (n + 1) * (n + 1) ≤
        (Fintype.card Q * Fintype.card B ^ (n + 1)) * (n + 1) := by
    simpa only [card_boundedTape, card_cfg] using
      Fintype.card_le_of_injective encode hinjective
  have hstrict :
      (Fintype.card Q * Fintype.card B ^ (n + 1)) * (n + 1) <
        Fintype.card A ^ (n + 1) * (n + 1) :=
    (Nat.mul_lt_mul_right (Nat.succ_pos n)).2 h
  exact (Nat.not_lt_of_ge hcard) hstrict

/-- For every fixed target alphabet, target state type, and tape length, some explicit finite
source alphabet has too much same-length tape information to inject into the target
configuration space. -/
public theorem exists_fin_no_injective_boundedTape_to_cfg
    (B Q : Type*) [Fintype B] [Fintype Q] (n : ℕ) :
    ∃ k : ℕ, ∀ encode : BoundedTape (Fin k) n → Cfg B Q n,
      ¬ Function.Injective encode := by
  let c := Fintype.card Q * Fintype.card B ^ (n + 1)
  refine ⟨c + 1, ?_⟩
  intro encode
  apply not_injective_boundedTape_to_cfg_of_card_lt (encode := encode)
  simp only [Fintype.card_fin]
  exact (Nat.lt_succ_self c).trans_le (Nat.le_pow (Nat.succ_pos n))

/-- If the source tape alphabet is strictly larger than the fixed target alphabet, then at some
tape length the target's fixed state space cannot compensate for the per-cell information
deficit. -/
public theorem exists_length_no_injective_boundedTape_to_cfg
    (hcard : Fintype.card B < Fintype.card A) :
    ∃ n : ℕ, ∀ encode : BoundedTape A n → Cfg B Q n,
      ¬ Function.Injective encode := by
  obtain ⟨n, hn⟩ := eventually_pow_dominates_mul
    (a := Fintype.card A) (b := Fintype.card B) (q := Fintype.card Q) hcard
  exact ⟨n, fun encode =>
    not_injective_boundedTape_to_cfg_of_card_lt hn encode⟩

/-- A fixed smaller target alphabet and fixed state type cannot provide injective same-length
encodings of source tapes at every tape length. -/
public theorem no_uniform_same_length_boundedTape_encoding
    (hcard : Fintype.card B < Fintype.card A) :
    ¬ ∃ encode : ∀ n, BoundedTape A n → Cfg B Q n,
      ∀ n, Function.Injective (encode n) := by
  rintro ⟨encode, hencode⟩
  obtain ⟨n, hnone⟩ :=
    exists_length_no_injective_boundedTape_to_cfg (A := A) (B := B) (Q := Q) hcard
  exact hnone (encode n) (hencode n)

/-! ## Any fixed linear expansion factor

`Cfg B Q (factor * (n + 1) - 1)` has exactly `factor * (n + 1)` tape cells when
`factor` is positive.  Thus one source cell over `A` has more information than a block of
`factor` target cells over `B` precisely when `|B| ^ factor < |A|`.  A fixed target state set
can compensate for that deficit only at finitely many lengths.
-/

/-- If the source alphabet carries more information per cell than a block of `factor` target
cells, then at some length even `factor` target cells per source cell, together with the fixed
target state set, cannot injectively encode every source bounded tape. -/
public theorem exists_length_no_injective_boundedTape_to_linearlyExpandedCfg
    (factor : ℕ) (hfactor : 0 < factor)
    (hcard : Fintype.card B ^ factor < Fintype.card A) :
    ∃ n : ℕ, ∀ encode :
        BoundedTape A n → Cfg B Q (factor * (n + 1) - 1),
      ¬ Function.Injective encode := by
  obtain ⟨n, hn⟩ := eventually_pow_dominates_mul
    (a := Fintype.card A)
    (b := Fintype.card B ^ factor)
    (q := Fintype.card Q * factor)
    hcard
  refine ⟨n, ?_⟩
  intro encode hinjective
  have hcells : factor * (n + 1) - 1 + 1 = factor * (n + 1) := by
    exact Nat.sub_add_cancel
      (Nat.succ_le_iff.mpr (Nat.mul_pos hfactor (Nat.succ_pos n)))
  have htargetSource :
      Fintype.card (Cfg B Q (factor * (n + 1) - 1)) <
        Fintype.card (BoundedTape A n) := by
    rw [card_cfg, card_boundedTape, hcells]
    have hfactorPow :
        (Fintype.card Q * Fintype.card B ^ (factor * (n + 1))) *
            (factor * (n + 1)) =
          ((Fintype.card Q * factor) *
            (Fintype.card B ^ factor) ^ (n + 1)) * (n + 1) := by
      rw [pow_mul]
      ac_rfl
    rw [hfactorPow]
    exact (Nat.mul_lt_mul_right (Nat.succ_pos n)).2 hn
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective encode hinjective)) htargetSource

/-- A fixed additive number of target cells does not repair a strict per-source-cell
information deficit.  At some source length, even `factor * (n + 1) + extra` target cells
cannot injectively hold all source bounded tapes. -/
public theorem exists_length_no_injective_boundedTape_to_affinelyExpandedCfg
    (factor extra : ℕ) (hfactor : 0 < factor)
    (hcard : Fintype.card B ^ factor < Fintype.card A) :
    ∃ n : ℕ, ∀ encode :
        BoundedTape A n → Cfg B Q (factor * (n + 1) + extra - 1),
      ¬ Function.Injective encode := by
  obtain ⟨n, hn⟩ := eventually_pow_dominates_mul
    (a := Fintype.card A)
    (b := Fintype.card B ^ factor)
    (q := Fintype.card Q * Fintype.card B ^ extra * (factor + extra))
    hcard
  refine ⟨n, ?_⟩
  intro encode hinjective
  let cells := factor * (n + 1) + extra
  have hcellsPos : 0 < cells := by
    dsimp [cells]
    exact Nat.add_pos_left (Nat.mul_pos hfactor (Nat.succ_pos n)) extra
  have hcellsIndex : cells - 1 + 1 = cells :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hcellsPos)
  have hcellsLe : cells ≤ (factor + extra) * (n + 1) := by
    dsimp [cells]
    nlinarith [Nat.le_mul_of_pos_left extra (Nat.succ_pos n)]
  have htargetSource :
      Fintype.card (Cfg B Q (cells - 1)) <
        Fintype.card (BoundedTape A n) := by
    rw [card_cfg, card_boundedTape, hcellsIndex]
    have hpow :
        Fintype.card B ^ cells =
          Fintype.card B ^ extra *
            (Fintype.card B ^ factor) ^ (n + 1) := by
      dsimp [cells]
      rw [pow_add, pow_mul]
      ac_rfl
    rw [hpow]
    calc
      (Fintype.card Q *
            (Fintype.card B ^ extra *
              (Fintype.card B ^ factor) ^ (n + 1))) *
          cells ≤
          ((Fintype.card Q * Fintype.card B ^ extra *
              (factor + extra)) *
            (Fintype.card B ^ factor) ^ (n + 1)) *
          (n + 1) := by
            rw [show
              (Fintype.card Q *
                    (Fintype.card B ^ extra *
                      (Fintype.card B ^ factor) ^ (n + 1))) *
                  cells =
                (Fintype.card Q * Fintype.card B ^ extra *
                    (Fintype.card B ^ factor) ^ (n + 1)) *
                  cells by ac_rfl]
            rw [show
              ((Fintype.card Q * Fintype.card B ^ extra *
                    (factor + extra)) *
                  (Fintype.card B ^ factor) ^ (n + 1)) *
                (n + 1) =
                (Fintype.card Q * Fintype.card B ^ extra *
                    (Fintype.card B ^ factor) ^ (n + 1)) *
                  ((factor + extra) * (n + 1)) by ac_rfl]
            exact Nat.mul_le_mul_left _ hcellsLe
      _ < Fintype.card A ^ (n + 1) * (n + 1) :=
        (Nat.mul_lt_mul_right (Nat.succ_pos n)).2 hn
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective encode hinjective)) htargetSource

/-- No single family of injective configuration encodings can use one fixed positive linear
expansion factor when a source cell has strictly more possibilities than the corresponding
target block. -/
public theorem no_uniform_linearExpansion_boundedTape_encoding
    (factor : ℕ) (hfactor : 0 < factor)
    (hcard : Fintype.card B ^ factor < Fintype.card A) :
    ¬ ∃ encode : ∀ n,
        BoundedTape A n → Cfg B Q (factor * (n + 1) - 1),
      ∀ n, Function.Injective (encode n) := by
  rintro ⟨encode, hencode⟩
  obtain ⟨n, hnone⟩ :=
    exists_length_no_injective_boundedTape_to_linearlyExpandedCfg
      (A := A) (B := B) (Q := Q) factor hfactor hcard
  exact hnone (encode n) (hencode n)

/-- No uniform family of injective configuration encodings can use one fixed affine cell
bound when a source cell has strictly more possibilities than a `factor`-cell target block. -/
public theorem no_uniform_affineExpansion_boundedTape_encoding
    (factor extra : ℕ) (hfactor : 0 < factor)
    (hcard : Fintype.card B ^ factor < Fintype.card A) :
    ¬ ∃ encode : ∀ n,
        BoundedTape A n → Cfg B Q (factor * (n + 1) + extra - 1),
      ∀ n, Function.Injective (encode n) := by
  rintro ⟨encode, hencode⟩
  obtain ⟨n, hnone⟩ :=
    exists_length_no_injective_boundedTape_to_affinelyExpandedCfg
      (A := A) (B := B) (Q := Q) factor extra hfactor hcard
  exact hnone (encode n) (hencode n)

/-- For every fixed target alphabet, state set, and positive linear expansion factor, there is
an explicit finite source alphabet for which no uniform family of injective encodings exists. -/
public theorem exists_fin_no_uniform_linearExpansion_boundedTape_encoding
    (B Q : Type*) [Fintype B] [Fintype Q]
    (factor : ℕ) (hfactor : 0 < factor) :
    ∃ k : ℕ, ¬ ∃ encode : ∀ n,
        BoundedTape (Fin k) n → Cfg B Q (factor * (n + 1) - 1),
      ∀ n, Function.Injective (encode n) := by
  refine ⟨Fintype.card B ^ factor + 1, ?_⟩
  apply no_uniform_linearExpansion_boundedTape_encoding
    (B := B) (Q := Q) factor hfactor
  simp only [Fintype.card_fin]
  exact Nat.lt_succ_self _

/-- For every fixed target alphabet, state set, positive linear factor, and additive cell
allowance, some finite source alphabet defeats every uniform affine injective encoding. -/
public theorem exists_fin_no_uniform_affineExpansion_boundedTape_encoding
    (B Q : Type*) [Fintype B] [Fintype Q]
    (factor extra : ℕ) (hfactor : 0 < factor) :
    ∃ k : ℕ, ¬ ∃ encode : ∀ n,
        BoundedTape (Fin k) n →
          Cfg B Q (factor * (n + 1) + extra - 1),
      ∀ n, Function.Injective (encode n) := by
  refine ⟨Fintype.card B ^ factor + 1, ?_⟩
  apply no_uniform_affineExpansion_boundedTape_encoding
    (B := B) (Q := Q) factor extra hfactor
  simp only [Fintype.card_fin]
  exact Nat.lt_succ_self _

end DLBA

end
