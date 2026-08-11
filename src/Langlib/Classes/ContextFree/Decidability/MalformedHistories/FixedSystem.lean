module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.LBA
public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.HistorySemantics
public import Langlib.Classes.ContextSensitive.Basics.ErasingImage
public import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
public import Langlib.Classes.RecursivelyEnumerable.Closure.Concatenation
public import Langlib.Classes.RecursivelyEnumerable.Closure.Substitution
public import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
public import Langlib.Classes.RecursivelyEnumerable.Examples.NonHalting
public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable

@[expose]
public section

/-!
# One fixed row system for the CFL-universality reduction

Rather than build a new bounded universal Turing machine, we use the existing
normal form saying that every RE language is the erasing image of a
context-sensitive language.  Applied once to a marked unary halting language,
this gives one fixed epsilon-free CS language and hence one fixed LBA.  A source
program affects only the regular predicate on the raw initial row: after
erasing `none` padding, that row must be `true :: false^encode(c)`.
-/

open Grammar.ErasingImage Relation

namespace ContextFree.MalformedHistories.FixedSystem

/-- The injective unary copy of the halting language over `Bool`. -/
def unaryHaltingBool : Language Bool :=
  Language.map (fun _ : Unit => false) haltingUnaryLanguage

/-- A leading marker makes every source word nonempty. -/
def markedHaltingLanguage : Language Bool :=
  ({[true]} : Language Bool) * unaryHaltingBool

/-- The marked unary word representing a source program. -/
def markedCodeWord (c : PartrecCode) : List Bool :=
  true :: (codeUnaryWord c).map fun _ => false

theorem markedCodeWord_mem_iff (c : PartrecCode) :
    markedCodeWord c ∈ markedHaltingLanguage ↔ (c.eval 0).Dom := by
  rw [markedHaltingLanguage, Language.mem_mul]
  constructor
  · rintro ⟨pre, hpre, suffix, hsuffix, happend⟩
    change pre = [true] at hpre
    subst pre
    change suffix ∈ Set.image (List.map fun _ : Unit => false)
      haltingUnaryLanguage at hsuffix
    obtain ⟨word, hword, rfl⟩ := hsuffix
    have htail : word = codeUnaryWord c := by
      have := List.cons.inj happend
      exact Function.Injective.list_map (fun _ _ _ => rfl) this.2
    subst word
    exact (codeUnaryWord_mem_haltingUnaryLanguage c).mp hword
  · intro hhalt
    refine ⟨[true], Set.mem_singleton _,
      (codeUnaryWord c).map (fun _ => false), ?_, rfl⟩
    change (codeUnaryWord c).map (fun _ => false) ∈
      Set.image (List.map fun _ : Unit => false) haltingUnaryLanguage
    exact ⟨codeUnaryWord c,
      (codeUnaryWord_mem_haltingUnaryLanguage c).mpr hhalt, rfl⟩

theorem markedHaltingLanguage_not_nil : [] ∉ markedHaltingLanguage := by
  rintro hnil
  rw [markedHaltingLanguage, Language.mem_mul] at hnil
  obtain ⟨pre, hpre, suffix, -, happend⟩ := hnil
  change pre = [true] at hpre
  subst pre
  simp at happend

theorem markedHaltingLanguage_is_RE : is_RE markedHaltingLanguage := by
  apply RE_of_RE_c_RE ({[true]} : Language Bool) unaryHaltingBool
  constructor
  · exact is_RE_of_isRegular (Language.isRegular_singleton_word [true])
  · exact RE_of_map_injective_RE (fun _ _ _ => rfl)
      haltingUnaryLanguage haltingUnaryLanguage_RE

section Machine

variable {Γ Λ : Type} [Fintype Γ] [Fintype Λ]
  [DecidableEq Γ] [DecidableEq Λ]

/-- Tape embedding supplied by the epsilon-free `CS = LBA` theorem. -/
def coverEmbed : Option Bool → Option ((Option Bool) ⊕ Γ) :=
  fun symbol => some (Sum.inl symbol)

/-- Turn the fixed cover LBA into the certified row system used by histories. -/
noncomputable def coverSystem
    (M : LBA.Machine (Option ((Option Bool) ⊕ Γ)) Λ) :=
  LBA.certifiedRowSystem M (coverEmbed (Γ := Γ))

/-- A raw first row whose padding erases to the prescribed marked word. -/
def InitialRow (target : List Bool)
    (row : List (LBA.RowCell (Option Bool)
      (Option ((Option Bool) ⊕ Γ)) Λ)) : Prop :=
  ∃ padded : List (Option Bool),
    row = padded.map LBA.RowCell.raw ∧
      padded.flatMap erasePadding = target

/-- For a fixed cover machine, valid histories exist exactly when the target
word belongs to the erasing image of its language. -/
theorem history_nonempty_iff_mem_erasingImage
    (M : LBA.Machine (Option ((Option Bool) ⊕ Γ)) Λ)
    (K : Language (Option Bool))
    (hM : LBA.LanguageViaEmbed M (coverEmbed (Γ := Γ)) = K)
    (target : List Bool) :
    (bundledValidLanguageWith (coverSystem M)
        (InitialRow (Γ := Γ) (Λ := Λ) target)).Nonempty ↔
      target ∈ K.homomorphicImage erasePadding := by
  rw [bundledValidLanguageWith_nonempty_iff]
  constructor
  · rintro ⟨first, hfirst, ⟨padded, rfl, herase⟩,
      last, hreach, hfinal⟩
    apply (Language.mem_homomorphicImage_iff_flatMap K erasePadding target).mpr
    refine ⟨padded, ?_, herase⟩
    rw [← hM, ← LBA.certifiedRowSystem_rowReachLanguage]
    refine ⟨?_, last, ?_, hfinal⟩
    · simpa using hfirst
    · simpa [coverSystem] using hreach
  · intro htarget
    obtain ⟨padded, hpadded, herase⟩ :=
      (Language.mem_homomorphicImage_iff_flatMap K erasePadding target).mp htarget
    have hrows : padded ∈ (coverSystem M).rowReachLanguage := by
      rw [coverSystem, LBA.certifiedRowSystem_rowReachLanguage, hM]
      exact hpadded
    obtain ⟨hpaddedne, last, hreach, hfinal⟩ := hrows
    refine ⟨padded.map LBA.RowCell.raw, ?_,
      ⟨padded, rfl, herase⟩, last, ?_, hfinal⟩
    · simpa using hpaddedne
    · simpa [coverSystem] using hreach

end Machine

/-- There is one fixed finite certified row system such that the only
source-dependent datum is the marked word tested on its raw initial row. -/
theorem exists_fixedSystem :
    ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
      (_ : DecidableEq Γ) (_ : DecidableEq Λ)
      (M : LBA.Machine (Option ((Option Bool) ⊕ Γ)) Λ),
      ∀ c : PartrecCode,
        (bundledValidLanguageWith (coverSystem M)
          (InitialRow (Γ := Γ) (Λ := Λ) (markedCodeWord c))).Nonempty ↔
            (c.eval 0).Dom := by
  obtain ⟨K, hKCS, himage⟩ :=
    is_RE_exists_CS_homomorphicImage markedHaltingLanguage_is_RE
  have hKne : [] ∉ K := by
    intro hnil
    have himageNil : [] ∈ K.homomorphicImage erasePadding :=
      (Language.mem_homomorphicImage_iff_flatMap K erasePadding []).mpr
        ⟨[], hnil, rfl⟩
    rw [himage] at himageNil
    exact markedHaltingLanguage_not_nil himageNil
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ :=
    is_LBA_pos_of_isCS_not_nil hKCS hKne
  refine ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, ?_⟩
  letI := hΓ
  letI := hΛ
  letI := hdΓ
  letI := hdΛ
  intro c
  rw [history_nonempty_iff_mem_erasingImage M K hM, himage]
  exact markedCodeWord_mem_iff c

end ContextFree.MalformedHistories.FixedSystem
