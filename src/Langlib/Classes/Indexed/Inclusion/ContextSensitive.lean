module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.FiniteLanguage
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.Indexed.Basics.FiniteSupport
public import Langlib.Grammars.Indexed.NormalForm.BoundedStackGrammar
public import Langlib.Grammars.Indexed.NormalForm.Shrinking
@[expose]
public section

/-! # Reducing indexed-to-CS inclusion to the finite normal-form core

The remaining constructive part of the inclusion `Indexed ⊆ CS` is the finite-alphabet,
finite-support, normal-form indexed grammar simulation. This file keeps the class-level
reduction explicit while the normal-form infrastructure is developed in the grammar modules.
-/

variable {T : Type}

/-- The LBA finite-normal-form core implies the context-sensitive finite-normal-form core. -/
public theorem finite_normalForm_CS_core_of_LBA_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) :
    ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language := by
  intro A _ _ _ g _ _ _ hNF
  exact is_LBA_pos_imp_isCS (hcore g hNF)

/-- Every fixed bounded-stack slice of a finite normal-form indexed grammar is recognized by
the bounded-tape LBA model, via the existing Kuroda construction for finite noncontracting
grammars. -/
public theorem is_LBA_pos_boundedStackGrammar_language_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    is_LBA_pos (grammar_language (IndexedGrammar.boundedStackGrammar g B)) := by
  classical
  haveI : Fintype (IndexedGrammar.BoundedStackNT g B) :=
    IndexedGrammar.boundedStackNTFintype (g := g) B
  have hfin : Finite (IndexedGrammar.boundedStackGrammar g B).nt := by
    change Finite (IndexedGrammar.BoundedStackNT g B)
    exact Finite.of_fintype _
  exact KurodaConstruction.noncontracting_finite_to_LBA
    (IndexedGrammar.boundedStackGrammar g B) hfin
    (IndexedGrammar.boundedStackGrammar_noncontracting hNF)

/-- The exact stack-bounded certificate slice of a finite normal-form indexed grammar is LBA:
it is the same language as the fixed bounded-stack grammar. -/
public theorem is_LBA_pos_stackBounded_certificate_language_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    is_LBA_pos
      ({w : List A | IndexedGrammar.NFYield.StackBounded g B g.initial [] w} :
        Language A) := by
  have hEq :
      grammar_language (IndexedGrammar.boundedStackGrammar g B) =
        ({w : List A | IndexedGrammar.NFYield.StackBounded g B g.initial [] w} :
          Language A) := by
    ext w
    exact IndexedGrammar.boundedStackGrammar_language_iff_stackBounded_certificate
      (g := g) hNF
  simpa [← hEq] using
    is_LBA_pos_boundedStackGrammar_language_of_isNormalForm (g := g) hNF B

/-- For a fixed flat tape bound, the bounded flat-path language is finite. The last node of
any accepting bounded flat path is the terminal encoding of the input word and is itself
inside `boundedFlatForms g B`, so the word length is at most `B`. -/
public theorem finite_boundedFlatPath_language
    {A : Type} [Fintype A]
    (g : IndexedGrammar A) (B : ℕ) :
    ((IndexedGrammar.boundedFlatPathLanguage g B : Language A) : Set (List A)).Finite :=
  IndexedGrammar.finite_boundedFlatPathLanguage g B

/-- Every fixed bounded-flat-path language is context-sensitive, because it is finite. -/
public theorem is_CS_boundedFlatPath_language
    {A : Type} [Fintype A]
    (g : IndexedGrammar A) (B : ℕ) :
    is_CS (IndexedGrammar.boundedFlatPathLanguage g B) :=
  is_CS_of_finite_language (finite_boundedFlatPath_language (g := g) B)

/-- A fixed bounded-flat-path slice of a normal-form indexed grammar does not contain `ε`. -/
public theorem not_nil_mem_boundedFlatPath_language_of_isNormalForm
    {A : Type} (g : IndexedGrammar A) [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    [] ∉ IndexedGrammar.boundedFlatPathLanguage g B := by
  intro hnil
  exact g.not_generates_nil_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF)
    (IndexedGrammar.boundedFlatPathLanguage_subset_language (g := g) (B := B) hnil)

/-- Every fixed bounded-flat-path slice of a normal-form indexed grammar is recognized by the
bounded-tape LBA model. -/
public theorem is_LBA_pos_boundedFlatPath_language_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    is_LBA_pos (IndexedGrammar.boundedFlatPathLanguage g B) :=
  is_LBA_pos_of_isCS_not_nil
    (is_CS_boundedFlatPath_language (g := g) B)
    (not_nil_mem_boundedFlatPath_language_of_isNormalForm (g := g) hNF B)

/-- On each fixed input-length ball, a finite normal-form indexed grammar agrees with one
fixed bounded-stack grammar, and that fixed slice is LBA-recognizable. -/
public theorem exists_LBA_pos_boundedStackGrammar_language_eq_on_length_le_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ,
      is_LBA_pos (grammar_language (IndexedGrammar.boundedStackGrammar g B)) ∧
        ∀ target : List A,
          target.length ≤ L →
          (target ∈ g.Language ↔
            target ∈ grammar_language (IndexedGrammar.boundedStackGrammar g B)) := by
  obtain ⟨B, hB⟩ :=
    IndexedGrammar.exists_bound_boundedStackGrammar_language_eq_on_length_le_isNormalForm
      (g := g) hNF L
  exact ⟨B, is_LBA_pos_boundedStackGrammar_language_of_isNormalForm (g := g) hNF B, hB⟩

/-- Flat-path finite-ball form of the current normal-form simulator: on every fixed
input-length ball, one finite bounded-flat-path slice agrees with the original normal-form
language, and that slice is LBA-recognizable. -/
public theorem exists_LBA_pos_boundedFlatPath_language_eq_on_length_le_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ,
      is_LBA_pos (IndexedGrammar.boundedFlatPathLanguage g B) ∧
        ∀ target : List A,
          target.length ≤ L →
          (target ∈ g.Language ↔ target ∈ IndexedGrammar.boundedFlatPathLanguage g B) := by
  obtain ⟨B, hB⟩ :=
    IndexedGrammar.exists_bound_boundedFlatPathLanguage_eq_on_length_le_isNormalForm
      (g := g) hNF L
  exact ⟨B, is_LBA_pos_boundedFlatPath_language_of_isNormalForm (g := g) hNF B, hB⟩

/-- Fixed packed flat-path slices are ε-free by construction. -/
public theorem not_nil_mem_packedFlatPathStackBound_language
    {A : Type} (g : IndexedGrammar A) (B : ℕ) :
    [] ∉ IndexedGrammar.packedFlatPathStackBoundLanguage g B :=
  IndexedGrammar.nil_not_mem_packedFlatPathStackBoundLanguage g B

/-- Fixed packed flat-path slices are sound for the original indexed grammar. -/
public theorem packedFlatPathStackBound_language_subset_language
    {A : Type} (g : IndexedGrammar A) (B : ℕ) :
    ∀ w : List A,
      w ∈ IndexedGrammar.packedFlatPathStackBoundLanguage g B →
      w ∈ g.Language :=
  fun _ h => IndexedGrammar.packedFlatPathStackBoundLanguage_subset_language h

/-- Fixed bounded-stack slices embed in the same-width packed flat-path language. -/
public theorem boundedStackGrammar_language_subset_packedFlatPathStackBound_language_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    ∀ w : List A,
      w ∈ grammar_language (IndexedGrammar.boundedStackGrammar g B) →
      w ∈ IndexedGrammar.packedFlatPathStackBoundLanguage g B :=
  fun _ h =>
    IndexedGrammar.boundedStackGrammar_language_subset_packedFlatPathStackBoundLanguage_isNormalForm
      (g := g) hNF h

/-- Packed flat-path witnesses decode to the length-scaled bounded-stack slice. -/
public theorem packedFlatPathStackBound_language_subset_boundedStackGrammar_language_length
    {A : Type} (g : IndexedGrammar A) [Fintype g.flag] (B : ℕ) :
    ∀ w : List A,
      w ∈ IndexedGrammar.packedFlatPathStackBoundLanguage g B →
      w ∈ grammar_language
        (IndexedGrammar.boundedStackGrammar g (w.length * (B + 2))) :=
  fun _ h =>
    IndexedGrammar.packedFlatPathStackBoundLanguage_subset_boundedStackGrammar_language_length
      (g := g) h

/-- Fixed-width terminal targets are sound for finite normal-form indexed grammars. -/
public theorem packedTerminalReverseRuleStep_language_subset_language_of_isNormalForm
    {A : Type} (g : IndexedGrammar A) [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    ∀ w : List A,
      w ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B →
      w ∈ g.Language :=
  fun _ h =>
    IndexedGrammar.packedTerminalReverseRuleStepLanguage_subset_language_of_isNormalForm
      (g := g) hNF h

/-- Fixed bounded-stack slices embed in the matching fixed-width terminal target. -/
public theorem boundedStackGrammar_language_subset_packedTerminalReverseRuleStep_language_of_isNormalForm
    {A : Type} (g : IndexedGrammar A) [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    ∀ w : List A,
      w ∈ grammar_language (IndexedGrammar.boundedStackGrammar g B) →
      w ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B :=
  fun _ h =>
    IndexedGrammar.boundedStackGrammar_language_subset_packedTerminalReverseRuleStepLanguage_isNormalForm
      (g := g) hNF h

/-- Fixed-width terminal-target witnesses decode to the length-scaled bounded-stack slice. -/
public theorem packedTerminalReverseRuleStep_language_subset_boundedStackGrammar_language_length
    {A : Type} (g : IndexedGrammar A) [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    ∀ w : List A,
      w ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B →
      w ∈ grammar_language
        (IndexedGrammar.boundedStackGrammar g (w.length * (B + 2))) :=
  fun _ h =>
    IndexedGrammar.packedTerminalReverseRuleStepLanguage_subset_boundedStackGrammar_language_length_isNormalForm
      (g := g) hNF h

/-- Packed-language finite-ball form of the current normal-form simulator target.

On every fixed input-length ball, one fixed stack-bound packed flat-path language agrees with
the original normal-form language. The remaining global core still has to turn this
length-parametric packed reachability family into one LBA/CS witness. -/
public theorem exists_packedFlatPathStackBound_language_eq_on_length_le_of_isNormalForm
    {A : Type} [Fintype A]
    (g : IndexedGrammar A) [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List A,
      target.length ≤ L →
      (target ∈ g.Language ↔
        target ∈ IndexedGrammar.packedFlatPathStackBoundLanguage g B) :=
  IndexedGrammar.exists_bound_packedFlatPathStackBoundLanguage_eq_on_length_le_isNormalForm
    (g := g) hNF L

/-- Fixed-width terminal-target finite-ball form of the current normal-form simulator target.

On every fixed input-length ball, one fixed packed width makes the normal-form language agree
with the terminal preimage of the reverse packed-rule row language. -/
public theorem exists_packedTerminalReverseRuleStep_language_eq_on_length_le_of_isNormalForm
    {A : Type} [Fintype A]
    (g : IndexedGrammar A) [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List A,
      target.length ≤ L →
      (target ∈ g.Language ↔
        target ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B) :=
  IndexedGrammar.exists_bound_packedTerminalReverseRuleStepLanguage_eq_on_length_le_isNormalForm
    (g := g) hNF L

/-- Concrete reverse-rule finite-ball form of the current simulator target.

On each fixed input-length ball, one packed width works for every target in the ball, and
membership is exactly reverse reachability by concrete normal-form rule steps. -/
public theorem exists_reverse_packedFlatRuleStep_eq_on_length_le_of_isNormalForm
    {A : Type} [Fintype A]
    (g : IndexedGrammar A) [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ B : ℕ, ∀ target : List A,
      target.length ≤ L →
      (target ∈ g.Language ↔
        ∃ htargetNe : target ≠ [],
          Relation.ReflTransGen
            (fun x y => IndexedGrammar.PackedFlatRuleStep g (B + 2) target.length y x)
            (IndexedGrammar.packedBoundedFlatForm g (B + 2) target.length
              ⟨target.map (IndexedGrammar.FlatSymbol.terminal (N := g.nt) (F := g.flag)),
                IndexedGrammar.terminal_mem_boundedFlatForms_length_mul
                  (g := g) (B := B) target⟩)
            (IndexedGrammar.packedBoundedFlatForm g (B + 2) target.length
              ⟨IndexedGrammar.encodeSentential
                  ([IndexedGrammar.ISym.indexed g.initial []] : List g.ISym),
                IndexedGrammar.initial_mem_boundedFlatForms_length_mul_of_pos
                  (g := g) (B := B) (w := target)
                  (List.length_pos_of_ne_nil htargetNe)⟩)) :=
  IndexedGrammar.exists_bound_reverse_packedFlatRuleStep_eq_on_length_le_isNormalForm
    (g := g) hNF L

/-- Exact concrete target for the finite normal-form core.

For a finite normal-form indexed grammar, membership is equivalent to the existence of a packed
width such that the terminal packed row reaches the initial packed row by reverse concrete
normal-form rule steps. This is the verifier-facing form of the remaining LBA/CS construction. -/
public theorem finite_normalForm_language_iff_exists_reverse_packedFlatRuleStep
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List A} :
    w ∈ g.Language ↔
      ∃ B : ℕ, ∃ hwne : w ≠ [],
        Relation.ReflTransGen
          (fun x y => IndexedGrammar.PackedFlatRuleStep g (B + 2) w.length y x)
          (IndexedGrammar.packedBoundedFlatForm g (B + 2) w.length
            ⟨w.map (IndexedGrammar.FlatSymbol.terminal (N := g.nt) (F := g.flag)),
              IndexedGrammar.terminal_mem_boundedFlatForms_length_mul
                (g := g) (B := B) w⟩)
          (IndexedGrammar.packedBoundedFlatForm g (B + 2) w.length
            ⟨IndexedGrammar.encodeSentential
                ([IndexedGrammar.ISym.indexed g.initial []] : List g.ISym),
              IndexedGrammar.initial_mem_boundedFlatForms_length_mul_of_pos
                (g := g) (B := B) (w := w)
                (List.length_pos_of_ne_nil hwne)⟩) :=
  IndexedGrammar.language_iff_exists_reverse_packedFlatRuleStep_isNormalForm
    (g := g) hNF

/-- Packed-cell tape-alphabet target for the finite normal-form core.

The terminal word is first represented as a list of packed cells. The remaining recognizer
target is the union over fixed widths of reverse packed-rule row languages. -/
public theorem finite_normalForm_language_iff_exists_packedTerminalCells_mem_reverseRuleStepRowLanguage
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List A} :
    w ∈ g.Language ↔
      ∃ B : ℕ,
        IndexedGrammar.packedTerminalCells g (B + 2) w ∈
          IndexedGrammar.packedReverseRuleStepRowLanguage g B :=
  IndexedGrammar.language_iff_exists_packedTerminalCells_mem_reverseRuleStepRowLanguage_isNormalForm
    (g := g) hNF

/-- Fixed-width terminal-language target for the finite normal-form core.

For a finite normal-form indexed grammar, membership is the union over fixed packed widths of
the terminal preimages of the reverse packed-rule row languages. -/
public theorem finite_normalForm_language_iff_exists_packedTerminalReverseRuleStepLanguage
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List A} :
    w ∈ g.Language ↔
      ∃ B : ℕ,
        w ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B :=
  IndexedGrammar.language_iff_exists_packedTerminalReverseRuleStepLanguage_isNormalForm
    (g := g) hNF

/-- Row-reachability expansion of the fixed-width terminal target.

This is the shape seen by a verifier on the terminal input: the input word is first packed into
fixed-width cells, and acceptance is reverse reachability from that packed row to the packed
initial row. -/
public theorem packedTerminalReverseRuleStep_language_iff_nonempty_packedCellsRow_reaches_initial
    {A : Type} (g : IndexedGrammar A) (B : ℕ) {w : List A} :
    w ∈ IndexedGrammar.packedTerminalReverseRuleStepLanguage g B ↔
      ∃ hwne : w ≠ [],
        Relation.ReflTransGen
          (fun x y =>
            IndexedGrammar.PackedFlatRuleStep g (B + 2)
              (IndexedGrammar.packedTerminalCells g (B + 2) w).length y x)
          (IndexedGrammar.packedCellsRow
            (IndexedGrammar.packedTerminalCells g (B + 2) w))
          (IndexedGrammar.packedBoundedFlatForm g (B + 2)
            (IndexedGrammar.packedTerminalCells g (B + 2) w).length
            ⟨IndexedGrammar.encodeSentential
                ([IndexedGrammar.ISym.indexed g.initial []] : List g.ISym),
              IndexedGrammar.initial_mem_boundedFlatForms_mul_of_pos
                (g := g) (B := B)
                (List.length_pos_of_ne_nil
                  ((IndexedGrammar.packedTerminalCells_ne_nil_iff g (B + 2)).mpr hwne))⟩) :=
  IndexedGrammar.packedTerminalReverseRuleStepLanguage_iff_nonempty_packedCellsRow_reaches_initial
    (g := g) B

/-- Concrete row-reachability target for the finite normal-form core.

For a finite normal-form indexed grammar, membership is equivalent to the existence of a fixed
packed width whose terminal packed row reaches the packed initial row by reverse concrete
normal-form steps. -/
public theorem finite_normalForm_language_iff_exists_nonempty_packedCellsRow_reaches_initial
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) {w : List A} :
    w ∈ g.Language ↔
      ∃ B : ℕ, ∃ hwne : w ≠ [],
        Relation.ReflTransGen
          (fun x y =>
            IndexedGrammar.PackedFlatRuleStep g (B + 2)
              (IndexedGrammar.packedTerminalCells g (B + 2) w).length y x)
          (IndexedGrammar.packedCellsRow
            (IndexedGrammar.packedTerminalCells g (B + 2) w))
          (IndexedGrammar.packedBoundedFlatForm g (B + 2)
            (IndexedGrammar.packedTerminalCells g (B + 2) w).length
            ⟨IndexedGrammar.encodeSentential
                ([IndexedGrammar.ISym.indexed g.initial []] : List g.ISym),
              IndexedGrammar.initial_mem_boundedFlatForms_mul_of_pos
                (g := g) (B := B)
                (List.length_pos_of_ne_nil
                  ((IndexedGrammar.packedTerminalCells_ne_nil_iff g (B + 2)).mpr hwne))⟩) := by
  rw [finite_normalForm_language_iff_exists_packedTerminalReverseRuleStepLanguage
    (g := g) hNF]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B,
      (packedTerminalReverseRuleStep_language_iff_nonempty_packedCellsRow_reaches_initial
        (g := g) (B := B)).mp hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨B,
      (packedTerminalReverseRuleStep_language_iff_nonempty_packedCellsRow_reaches_initial
        (g := g) (B := B)).mpr hB⟩

/-- If every finite-support normal-form indexed grammar over a finite inhabited alphabet is
context-sensitive, then every ε-free indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed_noEpsilon L) : is_CS L := by
  obtain ⟨A, hA, hAdec, hAinh, f, g, hnt, hflag, hdec, hNF, hmap⟩ :=
    is_Indexed_noEpsilon_exists_fintype_normalForm_image (L := L) hL
  haveI := hA
  haveI := hAdec
  haveI := hAinh
  haveI := hnt
  haveI := hflag
  haveI := hdec
  have hCSg : is_CS g.Language := hcore g hNF
  have hImage : is_CS (g.Language.homomorphicImage fun a => [f a]) :=
    is_CS_homomorphicImage_epsfree g.Language (fun a => [f a]) (fun _ => by simp) hCSg
  rw [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage
  rwa [hmap] at hImage

/-- If the finite normal-form indexed grammars are recognized by bounded-tape LBAs, then every
ε-free indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_LBA_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed_noEpsilon L) : is_CS L :=
  is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- Once epsilon elimination supplies an ε-free indexed witness for `L \ {ε}`, the existing
finite-normal-form core proves `L` context-sensitive. -/
public theorem is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hpart : is_Indexed_noEpsilon (L \ ({[]} : Set (List T)))) : is_CS L := by
  exact is_CS_of_diff_empty_of_is_CS
    (is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core hcore hpart)

/-- LBA-core variant of
`is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_LBA_core
    [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hpart : is_Indexed_noEpsilon (L \ ({[]} : Set (List T)))) : is_CS L :=
  is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hpart

/-- Epsilon elimination for indexed languages: the nonempty part of every indexed language has
an ε-free indexed grammar witness. -/
public theorem is_Indexed_noEpsilon_diff_empty {L : Language T}
    (hL : is_Indexed L) :
    is_Indexed_noEpsilon (L \ ({[]} : Set (List T))) := by
  obtain ⟨g, hg_lang⟩ := hL
  obtain ⟨g', hne', hlang'⟩ := g.exists_noEpsilon_preserving_nonempty
  refine ⟨g', hne', ?_⟩
  ext w
  by_cases hw : w = []
  · subst w
    constructor
    · intro hgen
      exact False.elim (g'.not_generates_nil_of_noEpsilon hne' hgen)
    · intro hwL
      exact False.elim (hwL.2 (by simp))
  · change g'.Generates w ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hlang' w hw]
    change w ∈ g.Language ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hg_lang]
    constructor
    · intro hgen
      exact ⟨hgen, by simpa [Set.mem_singleton_iff] using hw⟩
    · intro hmem
      exact hmem.1

/-- With epsilon elimination discharged, the remaining class-level indexed-to-CS reduction only
needs the finite normal-form core. -/
public theorem is_CS_of_is_Indexed_of_finite_normalForm_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L := by
  obtain ⟨A, hA, hAdec, hAinh, f, g, hnt, hflag, hdec, hNF, hmap⟩ :=
    is_Indexed_exists_fintype_normalForm_nonempty_image (L := L) hL
  haveI := hA
  haveI := hAdec
  haveI := hAinh
  haveI := hnt
  haveI := hflag
  haveI := hdec
  have hCSg : is_CS g.Language := hcore g hNF
  have hImage : is_CS (g.Language.homomorphicImage fun a => [f a]) :=
    is_CS_homomorphicImage_epsfree g.Language (fun a => [f a]) (fun _ => by simp) hCSg
  rw [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage
  rw [hmap] at hImage
  exact is_CS_of_diff_empty_of_is_CS hImage

/-- LBA-core variant of `is_CS_of_is_Indexed_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_finite_normalForm_LBA_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- If ε-elimination is proved for terminal-isolated, flag-separated grammars, then every
indexed language has an ε-free indexed witness for its nonempty part. -/
public theorem is_Indexed_noEpsilon_diff_empty_of_structural_epsilon_elim
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    {L : Language T} (hL : is_Indexed L) :
    is_Indexed_noEpsilon (L \ ({[]} : Set (List T))) := by
  obtain ⟨g, hg_lang⟩ := hL
  obtain ⟨g₀, hg₀_ti, hg₀_fs, _hg₀_fresh_of, hg₀_lang⟩ :=
    g.exists_terminalIsolated_flagsSeparated_all
  obtain ⟨g', hne', hlang'⟩ := helim g₀ hg₀_ti hg₀_fs
  refine ⟨g', hne', ?_⟩
  ext w
  by_cases hw : w = []
  · subst w
    constructor
    · intro hgen
      exact False.elim (g'.not_generates_nil_of_noEpsilon hne' hgen)
    · intro hwL
      exact False.elim (hwL.2 (by simp))
  · change g'.Generates w ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hlang' w hw, hg₀_lang w]
    change w ∈ g.Language ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hg_lang]
    constructor
    · intro hgen
      exact ⟨hgen, by simpa [Set.mem_singleton_iff] using hw⟩
    · intro hmem
      exact hmem.1

/-- Class-level reduction: arbitrary indexed languages reduce to the no-ε inclusion once the
epsilon-elimination theorem provides `L \ {ε}` as an ε-free indexed language. -/
public theorem is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core [Inhabited T]
    (helim : ∀ {L : Language T}, is_Indexed L →
      is_Indexed_noEpsilon (L \ ({[]} : Set (List T))))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core
    hcore (helim hL)

/-- LBA-core variant of
`is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_LBA_core [Inhabited T]
    (helim : ∀ {L : Language T}, is_Indexed L →
      is_Indexed_noEpsilon (L \ ({[]} : Set (List T))))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core
    helim (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- Class-level reduction using the structurally normalized ε-elimination target. -/
public theorem is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core
    [Inhabited T]
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core
    (fun h => is_Indexed_noEpsilon_diff_empty_of_structural_epsilon_elim helim h)
    hcore hL

/-- LBA-core variant of
`is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_LBA_core
    [Inhabited T]
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core
    helim (finite_normalForm_CS_core_of_LBA_core hcore) hL
