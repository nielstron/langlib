module

public import Langlib.Classes.ContextFree.Closure.Homomorphism
public import Langlib.Classes.ContextFree.Closure.Intersection
public import Langlib.Classes.ContextFree.Closure.Union
public import Langlib.Classes.DeterministicContextFree.Closure.Complement
public import Langlib.Classes.DeterministicContextFree.Closure.Intersection
public import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
public import Langlib.Classes.DeterministicContextFree.Closure.Concatenation
public import Langlib.Classes.DeterministicContextFree.Closure.Union
public import Langlib.Classes.DeterministicContextFree.Closure.UnionRegular
public import Langlib.Classes.DeterministicContextFree.Examples.AnBmCm
public import Langlib.Classes.DeterministicContextFree.Examples.AnBnCm
public import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
public import Langlib.Classes.Regular.Inclusion.DeterministicContextFree
public import Langlib.Classes.Regular.Closure.Concatenation
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Star

/-!
# Deterministic Context-Free Languages Are Not Closed Under Kleene Star

The proof uses the standard DCFL union witnesses, restricted to strictly positive
`a`, `b`, and `c` blocks.  The positive restriction prevents a later Kleene-star
slice from decomposing one `a+ b+ c+` payload into several witness blocks.
-/

namespace DCFStar

open PDA

/-- The regular slice `a+ b+ c+` over `Fin 3`. -/
public def abcPositive : Language (Fin 3) :=
  fun w => ∃ n m k : ℕ,
    w = List.replicate (n + 1) a_ ++
        List.replicate (m + 1) b_ ++
        List.replicate (k + 1) c_

public def lang_eq_any_pos : Language (Fin 3) :=
  lang_eq_any ⊓ abcPositive

public def lang_any_eq_pos : Language (Fin 3) :=
  lang_any_eq ⊓ abcPositive

public def lang_eq_eq_pos : Language (Fin 3) :=
  lang_eq_eq ⊓ abcPositive

private abbrev letterPlus (a : Fin 3) : Language (Fin 3) :=
  ({[a]} : Language (Fin 3)) * KStar.kstar ({[a]} : Language (Fin 3))

private lemma letterPlus_regular (a : Fin 3) :
    (letterPlus a).IsRegular :=
  (Language.isRegular_singleton_word [a]).mul'
    ((Language.isRegular_singleton_word [a]).kstar')

private lemma letterPlus_mem_iff {a : Fin 3} {w : List (Fin 3)} :
    w ∈ letterPlus a ↔ ∃ n : ℕ, w = List.replicate (n + 1) a := by
  have flatten_singletons :
      ∀ blocks : List (List (Fin 3)),
        (∀ y ∈ blocks, y = [a]) → blocks.flatten = List.replicate blocks.length a := by
    intro blocks
    induction blocks with
    | nil =>
        intro _
        simp
    | cons block blocks ih =>
        intro hblocks
        have hblock : block = [a] := hblocks block (by simp)
        have htail : ∀ y ∈ blocks, y = [a] := by
          intro y hy
          exact hblocks y (by simp [hy])
        simp [hblock, ih htail, List.replicate_succ]
  rw [letterPlus, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst u
    rw [Language.mem_kstar] at hv
    rcases hv with ⟨blocks, rfl, hblocks⟩
    have hblocks_eq : ∀ y ∈ blocks, y = [a] := by
      intro y hy
      exact Set.mem_singleton_iff.mp (hblocks y hy)
    exact ⟨blocks.length, by simp [flatten_singletons blocks hblocks_eq, List.replicate_succ]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨[a], Set.mem_singleton _, List.replicate n a, ?_, ?_⟩
    · rw [Language.mem_kstar]
      refine ⟨List.replicate n [a], ?_, ?_⟩
      · have hrep : (List.replicate n [a]).flatten = List.replicate n a := by
          induction n with
          | zero => rfl
          | succ n ih => simp [List.replicate_succ, ih]
        exact hrep.symm
      · intro y hy
        rw [List.mem_replicate] at hy
        exact hy.2.symm ▸ Set.mem_singleton [a]
    · simp [List.replicate_succ]

/-- The slice `a+ b+ c+` is regular. -/
public theorem abcPositive_regular : abcPositive.IsRegular := by
  have hreg : (letterPlus a_ * letterPlus b_ * letterPlus c_).IsRegular :=
    ((letterPlus_regular a_).mul' (letterPlus_regular b_)).mul' (letterPlus_regular c_)
  convert hreg using 1
  ext w
  constructor
  · rintro ⟨n, m, k, rfl⟩
    rw [Language.mem_mul]
    refine ⟨List.replicate (n + 1) a_ ++ List.replicate (m + 1) b_, ?_,
      List.replicate (k + 1) c_, (letterPlus_mem_iff).2 ⟨k, rfl⟩, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨List.replicate (n + 1) a_, (letterPlus_mem_iff).2 ⟨n, rfl⟩,
        List.replicate (m + 1) b_, (letterPlus_mem_iff).2 ⟨m, rfl⟩, rfl⟩
    · simp [List.append_assoc]
  · rw [Language.mem_mul]
    rintro ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_mul] at hu
    rcases hu with ⟨x, hx, y, hy, rfl⟩
    rcases (letterPlus_mem_iff).1 hx with ⟨n, rfl⟩
    rcases (letterPlus_mem_iff).1 hy with ⟨m, rfl⟩
    rcases (letterPlus_mem_iff).1 hv with ⟨k, rfl⟩
    exact ⟨n, m, k, by simp [List.append_assoc]⟩

public theorem DCF_lang_eq_any_pos : is_DCF lang_eq_any_pos :=
  DCF_inter_regular lang_eq_any abcPositive
    DCFLIntersection.DCF_lang_eq_any abcPositive_regular

public theorem DCF_lang_any_eq_pos : is_DCF lang_any_eq_pos :=
  DCF_inter_regular lang_any_eq abcPositive
    DCFLIntersection.DCF_lang_any_eq abcPositive_regular

public def lang_not_eq_any_pos : Language (Fin 3) :=
  lang_eq_any_posᶜ ⊓ abcPositive

public def lang_not_any_eq_pos : Language (Fin 3) :=
  lang_any_eq_posᶜ ⊓ abcPositive

public theorem DCF_lang_not_eq_any_pos : is_DCF lang_not_eq_any_pos :=
  DCF_inter_regular lang_eq_any_posᶜ abcPositive
    (DCF_closedUnderComplement lang_eq_any_pos DCF_lang_eq_any_pos)
    abcPositive_regular

public theorem DCF_lang_not_any_eq_pos : is_DCF lang_not_any_eq_pos :=
  DCF_inter_regular lang_any_eq_posᶜ abcPositive
    (DCF_closedUnderComplement lang_any_eq_pos DCF_lang_any_eq_pos)
    abcPositive_regular

private lemma lang_eq_eq_eq_pos_union_epsilon :
    lang_eq_eq = lang_eq_eq_pos + ({[]} : Language (Fin 3)) := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero =>
        right
        exact Set.mem_singleton []
    | succ n =>
        left
        constructor
        · exact ⟨n + 1, by rfl⟩
        · exact ⟨n, n, n, by simp [List.append_assoc]⟩
  · intro hw
    rw [Language.add_def] at hw
    rcases hw with hw | hw
    · exact hw.1
    · rw [Set.mem_singleton_iff] at hw
      subst w
      exact ⟨0, by simp⟩

public theorem notCF_lang_eq_eq_pos : ¬ is_CF lang_eq_eq_pos := by
  intro hpos
  apply notCF_lang_eq_eq
  rw [lang_eq_eq_eq_pos_union_epsilon]
  exact CF_of_CF_u_CF lang_eq_eq_pos ({[]} : Language (Fin 3))
    ⟨hpos, is_CF_singleton []⟩

public theorem notDCF_lang_eq_eq_pos : ¬ is_DCF lang_eq_eq_pos := by
  intro h
  exact notCF_lang_eq_eq_pos (is_CF_of_is_DCF h)

private lemma complement_not_pos_union_eq_eq_pos :
    (lang_not_eq_any_pos + lang_not_any_eq_pos)ᶜ ⊓ abcPositive = lang_eq_eq_pos := by
  ext w
  constructor
  · rintro ⟨hnotUnion, hpos⟩
    have hNotLeft : w ∉ lang_not_eq_any_pos := by
      intro hw
      exact hnotUnion (Or.inl hw)
    have hNotRight : w ∉ lang_not_any_eq_pos := by
      intro hw
      exact hnotUnion (Or.inr hw)
    have hEqAny : w ∈ lang_eq_any_pos := by
      by_contra h
      exact hNotLeft ⟨h, hpos⟩
    have hAnyEq : w ∈ lang_any_eq_pos := by
      by_contra h
      exact hNotRight ⟨h, hpos⟩
    exact ⟨lang_eq_eq_of_intersection ⟨hEqAny.1, hAnyEq.1⟩, hpos⟩
  · intro h
    constructor
    · intro hunion
      rw [Language.add_def] at hunion
      rcases hunion with hleft | hright
      · have hi := intersection_of_lang_eq_eq h.1
        exact hleft.1 ⟨hi.1, h.2⟩
      · have hi := intersection_of_lang_eq_eq h.1
        exact hright.1 ⟨hi.2, h.2⟩
    · exact h.2

private theorem notDCF_not_pos_union :
    ¬ is_DCF (lang_not_eq_any_pos + lang_not_any_eq_pos) := by
  intro hUnion
  have hComp : is_DCF (lang_not_eq_any_pos + lang_not_any_eq_pos)ᶜ :=
    DCF_closedUnderComplement (lang_not_eq_any_pos + lang_not_any_eq_pos) hUnion
  have hSlice : is_DCF ((lang_not_eq_any_pos + lang_not_any_eq_pos)ᶜ ⊓ abcPositive) :=
    DCF_inter_regular (lang_not_eq_any_pos + lang_not_any_eq_pos)ᶜ
      abcPositive hComp abcPositive_regular
  apply notDCF_lang_eq_eq_pos
  rwa [complement_not_pos_union_eq_eq_pos] at hSlice

private lemma lang_eq_eq_pos_of_intersection {w : List (Fin 3)}
    (h : w ∈ lang_eq_any_pos ⊓ lang_any_eq_pos) :
    w ∈ lang_eq_eq_pos := by
  exact ⟨lang_eq_eq_of_intersection ⟨h.1.1, h.2.1⟩, h.1.2⟩

private lemma intersection_of_lang_eq_eq_pos {w : List (Fin 3)}
    (h : w ∈ lang_eq_eq_pos) :
    w ∈ lang_eq_any_pos ⊓ lang_any_eq_pos := by
  have hi := intersection_of_lang_eq_eq h.1
  exact ⟨⟨hi.1, h.2⟩, ⟨hi.2, h.2⟩⟩

public theorem DCF_notClosedUnderUnion_pos :
    ¬ ClosedUnderUnion (α := Fin 3) is_DCF := by
  intro hclosed
  have hInter : is_DCF (lang_eq_any_pos ⊓ lang_any_eq_pos) := by
    rw [show lang_eq_any_pos ⊓ lang_any_eq_pos =
        (lang_eq_any_posᶜ + lang_any_eq_posᶜ)ᶜ by
      ext w
      simp only [Language.add_def]
      change w ∈ lang_eq_any_pos ∧ w ∈ lang_any_eq_pos ↔
        ¬ (w ∈ lang_eq_any_posᶜ ⊔ lang_any_eq_posᶜ)
      rw [show (lang_eq_any_posᶜ ⊔ lang_any_eq_posᶜ : Set (List (Fin 3))) =
        Set.union lang_eq_any_posᶜ lang_any_eq_posᶜ by rfl]
      change w ∈ lang_eq_any_pos ∧ w ∈ lang_any_eq_pos ↔
        ¬ (w ∉ lang_eq_any_pos ∨ w ∉ lang_any_eq_pos)
      tauto]
    exact DCF_closedUnderComplement (lang_eq_any_posᶜ + lang_any_eq_posᶜ)
      (hclosed lang_eq_any_posᶜ lang_any_eq_posᶜ
        (DCF_closedUnderComplement lang_eq_any_pos DCF_lang_eq_any_pos)
        (DCF_closedUnderComplement lang_any_eq_pos DCF_lang_any_eq_pos))
  apply notDCF_lang_eq_eq_pos
  convert hInter
  ext w
  constructor
  · exact intersection_of_lang_eq_eq_pos
  · exact lang_eq_eq_pos_of_intersection

private lemma abcPositive_pairwise {w : List (Fin 3)} (hw : w ∈ abcPositive) :
    w.Pairwise (· ≤ ·) := by
  rcases hw with ⟨n, m, k, rfl⟩
  simp +decide [List.pairwise_append, a_, b_, c_]

private lemma abcPositive_has_a {w : List (Fin 3)} (hw : w ∈ abcPositive) :
    a_ ∈ w := by
  rcases hw with ⟨n, m, k, rfl⟩
  simp [List.mem_append, List.mem_replicate, a_]

private lemma abcPositive_has_c {w : List (Fin 3)} (hw : w ∈ abcPositive) :
    c_ ∈ w := by
  rcases hw with ⟨n, m, k, rfl⟩
  simp [List.mem_append, List.mem_replicate, c_]

private lemma abcPositive_ne_nil {w : List (Fin 3)} (hw : w ∈ abcPositive) :
    w ≠ [] := by
  intro hnil
  have ha : a_ ∈ w := abcPositive_has_a hw
  simp [hnil] at ha

private lemma abcPositive_no_append_after_positive {u tail w : List (Fin 3)}
    (hu : u ∈ abcPositive) (ha : a_ ∈ tail) (hwEq : w = u ++ tail)
    (hw : w ∈ abcPositive) : False := by
  have hpair := abcPositive_pairwise hw
  rw [hwEq, List.pairwise_append] at hpair
  have hc : c_ ∈ u := abcPositive_has_c hu
  have hle : c_ ≤ a_ := hpair.2.2 c_ hc a_ ha
  have hnot : ¬ ((c_ : Fin 3) ≤ a_) := by decide
  exact hnot hle

private abbrev marker : Bool ⊕ Fin 3 := Sum.inl false

private lemma marker_not_mem_payload (w : List (Fin 3)) :
    (marker : Bool ⊕ Fin 3) ∉ w.map Sum.inr := by
  intro h
  rw [List.mem_map] at h
  rcases h with ⟨a, _ha, h⟩
  cases h

private abbrev payloadPositive : Language (Bool ⊕ Fin 3) :=
  Language.map Sum.inr abcPositive

private abbrev oneMarkerPositive : Language (Bool ⊕ Fin 3) :=
  ({[marker]} : Language (Bool ⊕ Fin 3)) * payloadPositive

private lemma payloadPositive_regular : payloadPositive.IsRegular :=
  abcPositive_regular.map Sum.inr

private lemma oneMarkerPositive_regular : oneMarkerPositive.IsRegular :=
  (Language.isRegular_singleton_word ([marker] : List (Bool ⊕ Fin 3))).mul'
    payloadPositive_regular

private lemma mem_oneMarkerPositive_iff {x : List (Bool ⊕ Fin 3)} :
    x ∈ oneMarkerPositive ↔
      ∃ w : List (Fin 3), x = marker :: w.map Sum.inr ∧ w ∈ abcPositive := by
  rw [oneMarkerPositive, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst u
    rcases hv with ⟨w, hw, rfl⟩
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨[marker], Set.mem_singleton _, w.map Sum.inr, ⟨w, hw, rfl⟩, rfl⟩

private def optionalMarkedLanguage (L₁ L₂ : Language (Fin 3)) :
    Language (Bool ⊕ Fin 3) :=
  {x | (∃ w, x = marker :: w.map Sum.inr ∧ w ∈ L₁) ∨
    (∃ w, x = w.map Sum.inr ∧ w ∈ L₂)}

private theorem DCF_optionalMarkedLanguage_pos :
    is_DCF (optionalMarkedLanguage lang_not_eq_any_pos lang_not_any_eq_pos) := by
  have hDCF :=
    DCFConcatenation.DCF_optional_marked_union
      DCF_lang_not_eq_any_pos DCF_lang_not_any_eq_pos
  simpa [optionalMarkedLanguage, marker] using hDCF

private def starSeed : Language (Bool ⊕ Fin 3) :=
  ({[marker]} : Language (Bool ⊕ Fin 3)) +
    optionalMarkedLanguage lang_not_eq_any_pos lang_not_any_eq_pos

private theorem DCF_starSeed : is_DCF starSeed :=
  DCF_regular_union ({[marker]} : Language (Bool ⊕ Fin 3))
    (optionalMarkedLanguage lang_not_eq_any_pos lang_not_any_eq_pos)
    (Language.isRegular_singleton_word [marker])
    DCF_optionalMarkedLanguage_pos

private lemma starSeed_mem_cases {x : List (Bool ⊕ Fin 3)} (hx : x ∈ starSeed) :
    x = [marker] ∨
      (∃ w, x = marker :: w.map Sum.inr ∧ w ∈ lang_not_eq_any_pos) ∨
      (∃ w, x = w.map Sum.inr ∧ w ∈ lang_not_any_eq_pos) := by
  simpa [starSeed, optionalMarkedLanguage, Language.add_def] using hx

private lemma starSeed_marker_free_payload {x : List (Bool ⊕ Fin 3)}
    (hx : x ∈ starSeed) (hfree : (marker : Bool ⊕ Fin 3) ∉ x) :
    ∃ w, x = w.map Sum.inr ∧ w ∈ lang_not_any_eq_pos := by
  rcases starSeed_mem_cases hx with hsingle | hmarked | hunmarked
  · subst x
    exact False.elim (hfree (by simp))
  · rcases hmarked with ⟨w, rfl, _hw⟩
    exact False.elim (hfree (by simp))
  · exact hunmarked

private lemma map_append_eq_map_split {u w : List (Fin 3)} {z : List (Bool ⊕ Fin 3)}
    (h : u.map Sum.inr ++ z = w.map Sum.inr) :
    ∃ v, w = u ++ v ∧ z = v.map Sum.inr := by
  induction u generalizing w with
  | nil =>
      exact ⟨w, by simp, by simpa using h⟩
  | cons a u ih =>
      cases w with
      | nil => simp at h
      | cons b w =>
          simp at h
          rcases h with ⟨hab, hrest⟩
          subst b
          rcases ih hrest with ⟨v, hv, hz⟩
          exact ⟨v, by simp [hv], hz⟩

private lemma payload_decomposition_of_marker_free_starSeed
    {blocks : List (List (Bool ⊕ Fin 3))} {w : List (Fin 3)}
    (hflat : blocks.flatten = w.map Sum.inr)
    (hblocks : ∀ b ∈ blocks, b ∈ starSeed) :
    ∃ payloads : List (List (Fin 3)),
      w = payloads.flatten ∧
      blocks = payloads.map (fun y => y.map Sum.inr) ∧
      ∀ y ∈ payloads, y ∈ lang_not_any_eq_pos := by
  induction blocks generalizing w with
  | nil =>
      cases w with
      | nil =>
          exact ⟨[], by simp, by simp, by simp⟩
      | cons a w =>
          simp at hflat
  | cons block rest ih =>
      have hblock : block ∈ starSeed := hblocks block (by simp)
      have hfree : (marker : Bool ⊕ Fin 3) ∉ block := by
        intro hm
        have hmem : (marker : Bool ⊕ Fin 3) ∈ (block :: rest).flatten :=
          List.mem_flatten.mpr ⟨block, by simp, hm⟩
        rw [hflat] at hmem
        exact marker_not_mem_payload w hmem
      rcases starSeed_marker_free_payload hblock hfree with ⟨u, hblockEq, hu⟩
      subst block
      have hsplit : ∃ v, w = u ++ v ∧ rest.flatten = v.map Sum.inr :=
        map_append_eq_map_split (by simpa using hflat)
      rcases hsplit with ⟨v, hw, hrestFlat⟩
      have hrestBlocks : ∀ b ∈ rest, b ∈ starSeed := by
        intro b hb
        exact hblocks b (by simp [hb])
      rcases ih hrestFlat hrestBlocks with ⟨payloads, hv, hrestEq, hpayloads⟩
      refine ⟨u :: payloads, ?_, ?_, ?_⟩
      · simp [hw, hv]
      · simp [hrestEq]
      · intro y hy
        have hy' : y = u ∨ y ∈ payloads := by simpa using hy
        rcases hy' with hEq | hy
        ·
          rw [hEq]
          exact hu
        · exact hpayloads _ hy

private lemma payloads_singleton_of_abcPositive
    {payloads : List (List (Fin 3))} {w : List (Fin 3)}
    (hwEq : w = payloads.flatten) (hw : w ∈ abcPositive)
    (hpayloads : ∀ y ∈ payloads, y ∈ lang_not_any_eq_pos) :
    ∃ u, payloads = [u] ∧ w = u ∧ u ∈ lang_not_any_eq_pos := by
  cases payloads with
  | nil =>
      have ha : a_ ∈ w := abcPositive_has_a hw
      simp [hwEq] at ha
  | cons u rest =>
      have hu : u ∈ lang_not_any_eq_pos := hpayloads u (by simp)
      cases rest with
      | nil =>
          exact ⟨u, by simp, by simpa using hwEq, hu⟩
      | cons v rest =>
          have hv : v ∈ lang_not_any_eq_pos := hpayloads v (by simp)
          have haTail : a_ ∈ (v :: rest).flatten := by
            rw [List.mem_flatten]
            exact ⟨v, by simp, abcPositive_has_a hv.2⟩
          exact False.elim <|
            abcPositive_no_append_after_positive hu.2 haTail (by simp [hwEq]) hw

private lemma marker_payload_mem_starSeed_iff {w : List (Fin 3)}
    (hw : w ∈ abcPositive) :
    marker :: w.map Sum.inr ∈ KStar.kstar starSeed ↔
      w ∈ lang_not_eq_any_pos ∨ w ∈ lang_not_any_eq_pos := by
  constructor
  · intro hstar
    rw [Language.mem_kstar] at hstar
    rcases hstar with ⟨blocks, hflat, hblocks⟩
    cases blocks with
    | nil =>
        simp at hflat
    | cons block rest =>
        have hblock : block ∈ starSeed := hblocks block (by simp)
        rcases starSeed_mem_cases hblock with hsingle | hmarked | hunmarked
        · subst block
          have hrestFlat : rest.flatten = w.map Sum.inr := by
            simpa using hflat.symm
          have hrestBlocks : ∀ b ∈ rest, b ∈ starSeed := by
            intro b hb
            exact hblocks b (by simp [hb])
          rcases payload_decomposition_of_marker_free_starSeed hrestFlat hrestBlocks with
            ⟨payloads, hwPayloads, _hrestEq, hpayloads⟩
          rcases payloads_singleton_of_abcPositive hwPayloads hw hpayloads with
            ⟨u, hpayloadsEq, hwEq, hu⟩
          right
          rwa [hwEq]
        · rcases hmarked with ⟨u, hblockEq, hu⟩
          subst block
          have hsplit : ∃ v, w = u ++ v ∧ rest.flatten = v.map Sum.inr :=
            map_append_eq_map_split (by simpa using hflat.symm)
          rcases hsplit with ⟨v, hwEq, hrestFlat⟩
          have hrestBlocks : ∀ b ∈ rest, b ∈ starSeed := by
            intro b hb
            exact hblocks b (by simp [hb])
          rcases payload_decomposition_of_marker_free_starSeed hrestFlat hrestBlocks with
            ⟨payloads, hvPayloads, _hrestEq, hpayloads⟩
          cases payloads with
          | nil =>
              left
              have hvNil : v = [] := by simpa using hvPayloads
              rwa [hwEq, hvNil, List.append_nil]
          | cons v₀ restPayloads =>
              have hv₀ : v₀ ∈ lang_not_any_eq_pos := hpayloads v₀ (by simp)
              have haTail : a_ ∈ (v₀ :: restPayloads).flatten := by
                rw [List.mem_flatten]
                exact ⟨v₀, by simp, abcPositive_has_a hv₀.2⟩
              have hvEq : v = (v₀ :: restPayloads).flatten := hvPayloads
              exact False.elim <|
                abcPositive_no_append_after_positive hu.2 (by simpa [hvEq] using haTail)
                  hwEq hw
        · rcases hunmarked with ⟨u, hblockEq, hu⟩
          subst block
          cases u with
          | nil =>
              exact False.elim (abcPositive_ne_nil hu.2 rfl)
          | cons a u =>
              simp at hflat
  · intro h
    rw [Language.mem_kstar]
    rcases h with h | h
    · refine ⟨[marker :: w.map Sum.inr], by simp, ?_⟩
      intro y hy
      rw [List.mem_singleton] at hy
      subst y
      exact Or.inr (Or.inl ⟨w, rfl, h⟩)
    · refine ⟨[[marker], w.map Sum.inr], by simp, ?_⟩
      intro y hy
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        exact Or.inl (Set.mem_singleton [marker])
      · rw [List.mem_singleton] at hy
        subst y
        exact Or.inr (Or.inr ⟨w, rfl, h⟩)

private theorem star_seed_slice_eq_union :
    [marker] \\ ((KStar.kstar starSeed) ⊓ oneMarkerPositive) =
      Language.map Sum.inr (lang_not_eq_any_pos + lang_not_any_eq_pos) := by
  ext x
  constructor
  · intro hx
    change marker :: x ∈ (KStar.kstar starSeed) ⊓ oneMarkerPositive at hx
    rcases hx with ⟨hstar, hone⟩
    rw [mem_oneMarkerPositive_iff] at hone
    rcases hone with ⟨w, hshape, hwpos⟩
    cases hshape
    rw [marker_payload_mem_starSeed_iff hwpos] at hstar
    exact ⟨w, by simpa [Language.add_def] using hstar, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwpos : w ∈ abcPositive := by
      rw [Language.add_def] at hw
      rcases hw with hw | hw
      · exact hw.2
      · exact hw.2
    change marker :: w.map Sum.inr ∈ (KStar.kstar starSeed) ⊓ oneMarkerPositive
    constructor
    · rw [marker_payload_mem_starSeed_iff hwpos]
      simpa [Language.add_def] using hw
    · rw [mem_oneMarkerPositive_iff]
      exact ⟨w, rfl, hwpos⟩

/-- Deterministic context-free languages over `Bool ⊕ Fin 3` are not closed
under Kleene star. -/
public theorem DCF_notClosedUnderKleeneStar :
    ¬ ClosedUnderKleeneStar (α := Bool ⊕ Fin 3) is_DCF := by
  intro hclosed
  have hStar : is_DCF (KStar.kstar starSeed) :=
    hclosed starSeed DCF_starSeed
  have hFiltered : is_DCF ((KStar.kstar starSeed) ⊓ oneMarkerPositive) :=
    DCF_inter_regular (KStar.kstar starSeed) oneMarkerPositive hStar
      oneMarkerPositive_regular
  have hQuot : is_DCF ([marker] \\ ((KStar.kstar starSeed) ⊓ oneMarkerPositive)) :=
    DCFHomomorphism.DCF_leftQuotient_singleton marker hFiltered
  rw [star_seed_slice_eq_union] at hQuot
  have hUnion : is_DCF (lang_not_eq_any_pos + lang_not_any_eq_pos) :=
    DCF_of_map_injective_DCF_rev (f := Sum.inr)
      (by
        intro a b h
        exact Sum.inr.inj h)
      (lang_not_eq_any_pos + lang_not_any_eq_pos) hQuot
  exact notDCF_not_pos_union hUnion

end DCFStar
