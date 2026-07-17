module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.LBA
public import Langlib.Automata.LinearBounded.RowEnumeration
import Mathlib.Tactic

@[expose]
public section

/-!
# Same-width resources for cofunctional LBA backtracking

This file records the finite-capacity facts needed by a deterministic implementation of
cofunctional-LBA acceptance.

A bounded configuration is encoded as one row cell per physical tape cell.  Every row cell stores
the tape symbol, a bit marking the head, and the (repeated) finite-control state.  This encoding is
injective.  Consequently, the number of bounded configurations is at most the number of rows of
the same width over `LBA.RowCell`.

The generic `RowNumeral.fuelCodec` uses digits of type `Option A`.  On every positive width its
capacity is strictly larger than the number of width-`n` rows over `A`.  Taking
`A = LBA.RowCell Unit Γ Λ` therefore gives enough same-width fuel to backtrack for every bounded
configuration, including the endpoint.  No extra physical tape cell is required; the encoded
configuration and fuel are merely constant many tracks in a finite product alphabet.

This is the resource lemma behind a direct cofunctional-LBA-to-DLBA compiler.  The compiler itself
is not constructed here.
-/

namespace LBA.CofunctionalResources

variable {Γ Λ : Type*}

/-- Pointwise, same-width row encoding of a bounded configuration.  The state is repeated in
every cell and the unique head position is marked by a Boolean. -/
@[expose]
public def encodeCfgCell {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) :
    LBA.RowCell Unit Γ Λ :=
  .cfg (cfg.tape.contents i) (decide (i = cfg.tape.head)) cfg.state

/-- The same-width configuration-row encoding is injective. -/
public theorem encodeCfgCell_injective {n : ℕ} [DecidableEq Γ] [DecidableEq Λ] :
    Function.Injective
      (encodeCfgCell (Γ := Γ) (Λ := Λ) :
        DLBA.Cfg Γ Λ n → Fin (n + 1) → LBA.RowCell Unit Γ Λ) := by
  rintro ⟨state₁, ⟨contents₁, head₁⟩⟩ ⟨state₂, ⟨contents₂, head₂⟩⟩ h
  have hheadCell := congrFun h head₁
  have hhead : head₁ = head₂ := by
    simp only [encodeCfgCell, decide_true, LBA.RowCell.cfg.injEq] at hheadCell
    exact of_decide_eq_true hheadCell.2.1.symm
  have hstate : state₁ = state₂ := by
    have hstateCell := congrFun h head₁
    simp only [encodeCfgCell, LBA.RowCell.cfg.injEq] at hstateCell
    exact hstateCell.2.2
  have hcontents : contents₁ = contents₂ := by
    funext i
    have hcell := congrFun h i
    simp only [encodeCfgCell, LBA.RowCell.cfg.injEq] at hcell
    exact hcell.1
  subst state₂
  subst contents₂
  subst head₂
  rfl

variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- Same-width rows over `LBA.RowCell` have room for every bounded configuration. -/
public theorem card_cfg_le_rowCapacity (n : ℕ) :
    Fintype.card (DLBA.Cfg Γ Λ n) ≤
      Fintype.card (LBA.RowCell Unit Γ Λ) ^ (n + 1) := by
  let encode :
      DLBA.Cfg Γ Λ n → Fin (n + 1) → LBA.RowCell Unit Γ Λ :=
    encodeCfgCell
  have hcard :
      Fintype.card (DLBA.Cfg Γ Λ n) ≤
        Fintype.card (Fin (n + 1) → LBA.RowCell Unit Γ Λ) :=
    Fintype.card_le_of_injective encode encodeCfgCell_injective
  simpa only [Fintype.card_pi_const] using hcard

/-- A width-preserving `Option RowCell` counter has strictly more values than there are bounded
configurations.  It can therefore count every possible predecessor step and still represent the
endpoint. -/
public theorem card_cfg_lt_fuelCapacity (n : ℕ) :
    Fintype.card (DLBA.Cfg Γ Λ n) <
      (RowNumeral.fuelCodec (LBA.RowCell Unit Γ Λ)).radix ^ (n + 1) :=
  (card_cfg_le_rowCapacity (Γ := Γ) (Λ := Λ) n).trans_lt
    (RowNumeral.rowCapacity_lt_fuelCapacity
      (LBA.RowCell Unit Γ Λ) (Nat.succ_pos n))

/-- Every backtracking depth up to the entire bounded configuration space is represented by a
same-width fuel row. -/
public theorem exists_fuelRow_of_le_card_cfg (n value : ℕ)
    (hvalue : value ≤ Fintype.card (DLBA.Cfg Γ Λ n)) :
    ∃ row : List (Option (LBA.RowCell Unit Γ Λ)),
      row.length = n + 1 ∧
        (RowNumeral.fuelCodec (LBA.RowCell Unit Γ Λ)).value row = value := by
  exact (RowNumeral.fuelCodec (LBA.RowCell Unit Γ Λ)).exists_row_of_value
    (lt_of_le_of_lt hvalue (card_cfg_lt_fuelCapacity (Γ := Γ) (Λ := Λ) n))

end LBA.CofunctionalResources

end
