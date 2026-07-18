module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Characterization
public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.ClassEquivalence

@[expose]
public section

/-!
# Complement counting does not remove the determinization frontier

The Immerman--Szelepcsényi compiler replaces a certified-row language `L` by
`Lᶜ \ {[]}`.  This is another nondeterministic certified-row reachability
language: the compiler makes the local verifier deterministic before installing
the counting protocol, but the protocol still guesses whole successor rows and
path witnesses.

This file makes the resulting barrier exact.  Every certified-row language
rejects the empty word, so applying the compiler twice recovers the original
language exactly.  Consequently, determinizing just the languages produced by
the complement compiler is equivalent to determinizing all certified-row
reachability languages, and hence to `LBA = DLBA`.
-/

open Classical

namespace CertifiedRowSystem

variable {I A C Q F : Type*}

namespace Complement

/-- The complement protocol alphabet is inhabited whenever its source alphabet
is inhabited.  This permits iterating the complement compiler without imposing
any cardinality lower bound beyond nonemptiness. -/
public noncomputable instance ProtocolCell.instNonempty
    {A : Type*} [Fintype A] [Nonempty A] :
    Nonempty (ProtocolCell A) :=
  ⟨inputProtocolCell
    (fun _ : Unit ↦ Classical.choice (inferInstance : Nonempty A)) ()⟩

end Complement

/-- The intrinsic positive-language side condition of certified-row reachability:
there is no width-zero input row in the language.  This is the side condition
that makes two applications of positive complementation involutive. -/
@[simp]
public theorem nil_not_mem_rowReachLanguage
    (S : CertifiedRowSystem I A C Q F) :
    [] ∉ S.rowReachLanguage := by
  rintro ⟨hne, _⟩
  exact hne rfl

/-- Applying the certified-row complement compiler twice recovers the source
row language exactly.  The first application produces `Lᶜ \ {[]}`; the second
produces `(Lᶜ \ {[]})ᶜ \ {[]}`, which equals `L` precisely because every
certified-row language rejects `[]`.

The source row alphabet is only required to be finite and inhabited, with no
lower cardinality bound. -/
public theorem rowReachLanguage_complementSystem_twice
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype C] [DecidableEq C]
    [Fintype Q] [DecidableEq Q]
    [Fintype F] [DecidableEq F]
    (S : CertifiedRowSystem I A C Q F) :
    (Complement.complementSystem
      (Complement.complementSystem S)).rowReachLanguage =
        S.rowReachLanguage := by
  classical
  rw [rowReachLanguage_complementSystem,
    rowReachLanguage_complementSystem]
  funext input
  apply propext
  change
    ((¬ ((¬ S.rowReachLanguage input) ∧ input ≠ [])) ∧ input ≠ []) ↔
      S.rowReachLanguage input
  constructor
  · rintro ⟨hnotComplement, hinput⟩
    by_contra hsource
    exact hnotComplement ⟨hsource, hinput⟩
  · intro hsource
    refine ⟨?_, ?_⟩
    · rintro ⟨hnotSource, _⟩
      exact hnotSource hsource
    · intro hnil
      subst input
      exact nil_not_mem_rowReachLanguage S hsource

/-- The apparent restricted target of determinizing only outputs of the
Immerman--Szelepcsényi row compiler.  The quantification is uniform over all
finite source alphabets, certificate alphabets, and verifier types; the row
alphabet merely has to be inhabited so that the counting radix is nontrivial. -/
public def EveryComplementSystemRowReachLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A C Q F : Type)
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype C] [DecidableEq C]
    [Fintype Q] [DecidableEq Q]
    [Fintype F] [DecidableEq F]
    (S : CertifiedRowSystem T A C Q F),
    is_DLBA (Complement.complementSystem S).rowReachLanguage

/-- The same complement-output frontier stated in the exact-two-matching
language class.  Since `TwoMatchingLBA = DLBA`, this does not weaken the
determinization obligation: it asks for an exact two-matching presentation of
every counting-protocol output. -/
public def EveryComplementSystemRowReachLanguageIsTwoMatchingLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A C Q F : Type)
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype C] [DecidableEq C]
    [Fintype Q] [DecidableEq Q]
    [Fintype F] [DecidableEq F]
    (S : CertifiedRowSystem T A C Q F),
    is_TwoMatchingLBA
      (Complement.complementSystem S).rowReachLanguage

private theorem emptyLanguage_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    is_DLBA (⊥ : Language T) := by
  let M : DLBA.Machine (Option (T ⊕ Unit)) Unit :=
    { transition := fun _ _ ↦ none
      accept := fun _ ↦ false
      initial := () }
  refine
    ⟨Unit, Unit, inferInstance, inferInstance, inferInstance,
      inferInstance, false, M, ?_⟩
  funext input
  apply propext
  change DLBA.LanguageRecognized M
    (fun symbol ↦ some (Sum.inl symbol)) false input ↔ False
  simp [DLBA.LanguageRecognized, DLBA.LanguageViaEmbed, DLBA.Accepts, M]

/-- Complement-protocol outputs are determinization-universal: asking for a
DLBA presentation only for those outputs is already equivalent to asking for
one for every certified-row reachability language.

For an inhabited row alphabet, the reverse direction applies the assumed
determinizer to the complement output of `complementSystem S`, then uses
`rowReachLanguage_complementSystem_twice`.  If the row alphabet is empty, the
source row language itself is empty, so no exceptional terminal-alphabet
cardinality assumption is needed. -/
public theorem
    everyComplementSystemRowReachLanguage_iff_certifiedRowReachLanguage
    {T : Type} [Fintype T] [DecidableEq T] :
    EveryComplementSystemRowReachLanguageIsDLBA T ↔
      EveryCertifiedRowReachLanguageIsDLBA T := by
  constructor
  · intro hcomplement A C Q F hA hC hQ hF hdecA hdecC hdecQ hdecF S
    letI := hA
    letI := hC
    letI := hQ
    letI := hF
    letI := hdecA
    letI := hdecC
    letI := hdecQ
    letI := hdecF
    by_cases hnonempty : Nonempty A
    · letI : Nonempty A := hnonempty
      let first := Complement.complementSystem S
      have htwice :
          is_DLBA
            (Complement.complementSystem first).rowReachLanguage :=
        hcomplement
          (Complement.ProtocolCell A)
          Complement.ProtocolAction
          (Complement.ProtocolVerifier (Finset Q) F)
          Bool first
      rw [show (Complement.complementSystem first).rowReachLanguage =
          S.rowReachLanguage by
        simpa only [first] using
          rowReachLanguage_complementSystem_twice S] at htwice
      exact htwice
    · have hempty : S.rowReachLanguage = (⊥ : Language T) := by
        funext input
        apply propext
        change input ∈ S.rowReachLanguage ↔ False
        constructor
        · rintro ⟨hinput, _⟩
          obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hinput
          exact hnonempty ⟨S.inputCell first⟩
        · exact False.elim
      rw [hempty]
      exact emptyLanguage_is_DLBA
  · intro hall A C Q F hA hnonemptyA hdecA hC hdecC hQ hdecQ hF hdecF S
    letI := hA
    letI := hnonemptyA
    letI := hdecA
    letI := hC
    letI := hdecC
    letI := hQ
    letI := hdecQ
    letI := hF
    letI := hdecF
    exact hall
      (Complement.ProtocolCell A)
      Complement.ProtocolAction
      (Complement.ProtocolVerifier (Finset Q) F)
      Bool
      (Complement.complementSystem S)

/-- Exact class-level barrier: a DLBA construction for every output of the
Immerman--Szelepcsényi certified-row compiler would solve the first LBA problem,
and conversely `LBA = DLBA` would determinize every such output. -/
public theorem lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsDLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryComplementSystemRowReachLanguageIsDLBA T := by
  rw [lba_eq_dlba_iff_certifiedRowReach]
  exact
    everyComplementSystemRowReachLanguage_iff_certifiedRowReachLanguage.symm

/-- Asking for an exact-two-matching presentation of every
Immerman--Szelepcsényi compiler output is equivalent to asking for a DLBA
presentation of every output. -/
public theorem
    everyComplementSystemRowReachLanguageIsTwoMatchingLBA_iff_dlba
    {T : Type} [Fintype T] [DecidableEq T] :
    EveryComplementSystemRowReachLanguageIsTwoMatchingLBA T ↔
      EveryComplementSystemRowReachLanguageIsDLBA T := by
  constructor
  · intro htwo A C Q F hA hnonemptyA hdecA hC hdecC hQ hdecQ hF hdecF S
    letI := hA
    letI := hnonemptyA
    letI := hdecA
    letI := hC
    letI := hdecC
    letI := hQ
    letI := hdecQ
    letI := hF
    letI := hdecF
    have hmem :
        (Complement.complementSystem S).rowReachLanguage ∈
          (TwoMatchingLBA : Set (Language T)) :=
      htwo A C Q F S
    rw [TwoMatchingLBA_eq_DLBA] at hmem
    exact hmem
  · intro hdlba A C Q F hA hnonemptyA hdecA hC hdecC hQ hdecQ hF hdecF S
    letI := hA
    letI := hnonemptyA
    letI := hdecA
    letI := hC
    letI := hdecC
    letI := hQ
    letI := hdecQ
    letI := hF
    letI := hdecF
    have hmem :
        (Complement.complementSystem S).rowReachLanguage ∈
          (DLBA : Set (Language T)) :=
      hdlba A C Q F S
    rw [← TwoMatchingLBA_eq_DLBA] at hmem
    exact hmem

/-- Direct three-to-two frontier for the complement route: compiling all
Immerman--Szelepcsényi row languages to exact two-matching LBAs is equivalent
to the full equality `LBA = DLBA`.  Thus complement counting followed by a
two-matching conversion would not be a restricted shortcut; it would solve the
remaining open inclusion. -/
public theorem
    lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryComplementSystemRowReachLanguageIsTwoMatchingLBA T := by
  rw [
    everyComplementSystemRowReachLanguageIsTwoMatchingLBA_iff_dlba]
  exact lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsDLBA

end CertifiedRowSystem

end
