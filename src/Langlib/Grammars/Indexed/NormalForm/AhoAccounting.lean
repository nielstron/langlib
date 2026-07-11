module

public import Langlib.Grammars.Indexed.NormalForm.AhoCertificate

@[expose]
public section

/-!
# Finite accounting for Aho's linear-space simulation

The semantic part of Aho's argument associates every live nonterminal and every surviving
compressed flag with a distinct terminal position of the target word.  This file isolates the
finite arithmetic needed after those two associations have been constructed.

There are two independent injections into `Fin n`, so there are at most `2 * n` payload symbols.
If every payload symbol owns at most one surrounding `$`/`¢` frame, and the whole tape has two
fixed boundary symbols, its length is at most `6 * n + 2`, hence at most `8 * n` for `n > 0`.

The interval API below is a small convenience for constructing the ownership injections.  Live
parse tasks naturally own disjoint, nonempty yield intervals, whose left endpoints are distinct
terminal positions.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Charges into terminal positions -/

/-- A proof-relevant injection of a finite family of objects into `n` terminal positions. -/
public structure Charge (X : Type*) (n : ℕ) where
  owner : X → Fin n
  owner_injective : Function.Injective owner

namespace Charge

/-- A charged finite family contains no more objects than terminal positions. -/
public theorem card_le {X : Type*} [Fintype X] {n : ℕ} (c : Charge X n) :
    Fintype.card X ≤ n := by
  simpa using Fintype.card_le_of_injective c.owner c.owner_injective

/-- Transport a charge along an injective map into an already charged family. -/
public def comap {X Y : Type*} {n : ℕ} (c : Charge Y n) (f : X → Y)
    (hf : Function.Injective f) : Charge X n where
  owner := c.owner ∘ f
  owner_injective := c.owner_injective.comp hf

/-- Restrict a charge to a subtype. -/
public def subtype {X : Type*} {n : ℕ} (c : Charge X n) (p : X → Prop) :
    Charge {x // p x} n :=
  c.comap Subtype.val Subtype.val_injective

end Charge

/-- A list has length at most `n` whenever its positions inject into `Fin n`. -/
public theorem list_length_le_of_position_charge {X : Type*} {n : ℕ} (xs : List X)
    (owner : Fin xs.length → Fin n) (hinj : Function.Injective owner) :
    xs.length ≤ n := by
  simpa using Fintype.card_le_of_injective owner hinj

/-! ## Nonempty disjoint yield intervals -/

/-- A nonempty half-open interval `[lo, hi)` inside `Fin n`. -/
public structure YieldInterval (n : ℕ) where
  lo : ℕ
  hi : ℕ
  nonempty : lo < hi
  upper : hi ≤ n

namespace YieldInterval

/-- The first terminal position owned by a nonempty yield interval. -/
public def owner {n : ℕ} (I : YieldInterval n) : Fin n :=
  ⟨I.lo, lt_of_lt_of_le I.nonempty I.upper⟩

/-- Two half-open intervals are ordered without overlap. -/
public def Disjoint {n : ℕ} (I J : YieldInterval n) : Prop :=
  I.hi ≤ J.lo ∨ J.hi ≤ I.lo

public theorem disjoint_comm {n : ℕ} {I J : YieldInterval n} :
    Disjoint I J ↔ Disjoint J I := by
  simp only [Disjoint, or_comm]

/-- Disjoint nonempty intervals have different first positions. -/
public theorem owner_ne_of_disjoint {n : ℕ} {I J : YieldInterval n}
    (h : Disjoint I J) : I.owner ≠ J.owner := by
  intro howner
  have hlo : I.lo = J.lo := by
    simpa [owner] using congrArg Fin.val howner
  rcases h with hIJ | hJI
  · rw [← hlo] at hIJ
    exact (Nat.not_lt_of_ge hIJ) I.nonempty
  · rw [hlo] at hJI
    exact (Nat.not_lt_of_ge hJI) J.nonempty

/-- Pairwise-disjoint nonempty intervals induce an injective charge by left endpoints. -/
public def chargeOfPairwiseDisjoint {X : Type*} {n : ℕ}
    (span : X → YieldInterval n)
    (hspan : Pairwise fun x y => Disjoint (span x) (span y)) : Charge X n where
  owner := fun x => (span x).owner
  owner_injective := by
    intro x y howner
    by_contra hxy
    exact owner_ne_of_disjoint (hspan hxy) howner

/-- The whole nonempty terminal range. -/
public def whole (n : ℕ) (hn : 0 < n) : YieldInterval n where
  lo := 0
  hi := n
  nonempty := hn
  upper := le_rfl

/-- The prefix interval obtained by splitting at an interior midpoint. -/
public def left {n : ℕ} (I : YieldInterval n) (mid : ℕ)
    (hlo : I.lo < mid) (hhi : mid < I.hi) : YieldInterval n where
  lo := I.lo
  hi := mid
  nonempty := hlo
  upper := le_trans (Nat.le_of_lt hhi) I.upper

/-- The suffix interval obtained by splitting at an interior midpoint. -/
public def right {n : ℕ} (I : YieldInterval n) (mid : ℕ)
    (_hlo : I.lo < mid) (hhi : mid < I.hi) : YieldInterval n where
  lo := mid
  hi := I.hi
  nonempty := hhi
  upper := I.upper

/-- The two pieces of an interior split are disjoint. -/
public theorem disjoint_left_right {n : ℕ} (I : YieldInterval n) (mid : ℕ)
    (hlo : I.lo < mid) (hhi : mid < I.hi) :
    Disjoint (I.left mid hlo hhi) (I.right mid hlo hhi) := by
  left
  exact le_rfl

/-- Shift an interval right into a possibly larger ambient range. -/
public def shift {n m : ℕ} (I : YieldInterval n) (offset : ℕ)
    (hupper : offset + I.hi ≤ m) : YieldInterval m where
  lo := offset + I.lo
  hi := offset + I.hi
  nonempty := Nat.add_lt_add_left I.nonempty offset
  upper := hupper

/-- Shifting both intervals by the same offset preserves disjointness. -/
public theorem disjoint_shift {n m : ℕ} {I J : YieldInterval n} (offset : ℕ)
    (hI : offset + I.hi ≤ m) (hJ : offset + J.hi ≤ m)
    (h : Disjoint I J) :
    Disjoint (I.shift offset hI) (J.shift offset hJ) := by
  rcases h with h | h
  · left
    simpa [shift] using Nat.add_le_add_left h offset
  · right
    simpa [shift] using Nat.add_le_add_left h offset

/-- The left yield of a binary event occupies `[0, |u|)` in the concatenated yield. -/
public def appendLeft {α : Type*} (u v : List α) (hu : 0 < u.length) :
    YieldInterval (u ++ v).length where
  lo := 0
  hi := u.length
  nonempty := hu
  upper := by simp

/-- The right yield of a binary event occupies `[|u|, |u| + |v|)`. -/
public def appendRight {α : Type*} (u v : List α) (hv : 0 < v.length) :
    YieldInterval (u ++ v).length where
  lo := u.length
  hi := (u ++ v).length
  nonempty := by simp [List.length_append, hv]
  upper := le_rfl

/-- The canonical child intervals of a productive binary event are disjoint. -/
public theorem disjoint_appendLeft_appendRight {α : Type*} (u v : List α)
    (hu : 0 < u.length) (hv : 0 < v.length) :
    Disjoint (appendLeft u v hu) (appendRight u v hv) := by
  left
  exact le_rfl

end YieldInterval

/-! ## Parse-facing interval conveniences -/

end Aho

namespace NFParse

/-- Every concrete normal-form parse has a positive-length yield. -/
public theorem yield_length_pos
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) : 0 < w.length :=
  NFYield.yield_length_pos p.toNFYield

/-- The root task of a parse owns its whole nonempty yield interval. -/
public def wholeYieldInterval
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) : Aho.YieldInterval w.length :=
  Aho.YieldInterval.whole w.length (yield_length_pos p)

end NFParse

namespace Aho

/-! ## Payload and framed-tape accounting -/

/-- Separate terminal-position charges for live nonterminal/task occurrences and compressed-flag
occurrences.  The two families may reuse terminal positions across kinds; injectivity is needed
within each kind only. -/
public structure TokenAccounting (Task FlagToken : Type*) (n : ℕ) where
  taskCharge : Charge Task n
  flagCharge : Charge FlagToken n

namespace TokenAccounting

variable {Task FlagToken : Type*} [Fintype Task] [Fintype FlagToken] {n : ℕ}

/-- Number of live task and compressed-flag payload symbols. -/
public def payloadCount (_a : TokenAccounting Task FlagToken n) : ℕ :=
  Fintype.card Task + Fintype.card FlagToken

/-- Two independent injections into `Fin n` give at most `2*n` payload symbols. -/
public theorem payloadCount_le_two_mul (a : TokenAccounting Task FlagToken n) :
    a.payloadCount ≤ 2 * n := by
  have htask := a.taskCharge.card_le
  have hflag := a.flagCharge.card_le
  simp only [payloadCount]
  omega

end TokenAccounting

/-- Complete counting data for an Aho work tape.  `frameCount` counts matched `$`/`¢` pairs;
the inequality records that each pair is charged to a different payload occurrence. -/
public structure TapeAccounting (Task FlagToken : Type*)
    [Fintype Task] [Fintype FlagToken] (n : ℕ) where
  tokens : TokenAccounting Task FlagToken n
  frameCount : ℕ
  frameCount_le_payload : frameCount ≤ tokens.payloadCount

namespace TapeAccounting

variable {Task FlagToken : Type*} [Fintype Task] [Fintype FlagToken] {n : ℕ}

/-- Payload symbols, two delimiters per frame, and two fixed tape-boundary symbols. -/
public def cellCount (a : TapeAccounting Task FlagToken n) : ℕ :=
  a.tokens.payloadCount + 2 * a.frameCount + 2

/-- The direct Aho count before absorbing the two fixed boundary symbols. -/
public theorem cellCount_le_six_mul_add_two (a : TapeAccounting Task FlagToken n) :
    a.cellCount ≤ 6 * n + 2 := by
  have hpayload := a.tokens.payloadCount_le_two_mul
  have hframes := a.frameCount_le_payload
  simp only [cellCount]
  omega

/-- A convenient integral-cell version of Aho's linear bound.  For a nonempty target, eight
virtual work symbols per input cell accommodate all payloads, frames, and boundary symbols. -/
public theorem cellCount_le_eight_mul (a : TapeAccounting Task FlagToken n) (hn : 0 < n) :
    a.cellCount ≤ 8 * n := by
  have h := a.cellCount_le_six_mul_add_two
  omega

end TapeAccounting

/-- Direct arithmetic form for clients that already know payload and frame counts. -/
public theorem framed_cell_count_le_eight_mul {payload frames n : ℕ}
    (hpayload : payload ≤ 2 * n) (hframes : frames ≤ payload) (hn : 0 < n) :
    payload + 2 * frames + 2 ≤ 8 * n := by
  omega

end Aho
end IndexedGrammar
