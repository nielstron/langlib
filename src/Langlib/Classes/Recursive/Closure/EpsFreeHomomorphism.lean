module

public import Langlib.Classes.Recursive.Decidability.Membership
import Langlib.Utilities.PrimrecHelpers
import Mathlib.Tactic

/-!
# Recursive Closure Under ε-Free Homomorphism

This file proves that recursive languages over finite alphabets are closed under
ε-free string homomorphisms.

For a target word `u`, any source word `w` with `w.flatMap h = u` has
`w.length ≤ u.length`, because each source symbol maps to a nonempty word.  The
decider therefore enumerates all source words of length at most `u.length`, tests
membership in the original recursive language, and checks `w.flatMap h = u`.
-/

variable {α β : Type}

private def wordsOfLen (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => (wordsOfLen alphabet k).flatMap fun w => alphabet.map fun a => a :: w

private def wordsUpTo (alphabet : List α) (n : ℕ) : List (List α) :=
  (List.range (n + 1)).flatMap (wordsOfLen alphabet)

private theorem wordsOfLen_eq (alphabet : List α) (n : ℕ) :
    wordsOfLen alphabet n =
      Nat.rec (motive := fun _ => List (List α)) [[]]
        (fun _ ih => ih.flatMap fun w => alphabet.map fun a => a :: w) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [wordsOfLen, ih]

private theorem wordsOfLen_primrec [Primcodable α] :
    Primrec (fun x : List α × ℕ => wordsOfLen x.1 x.2) := by
  have hstep : Primrec₂ (fun (a : List α × ℕ) (q : ℕ × List (List α)) =>
      q.2.flatMap fun w => a.1.map fun s => s :: w) := by
    apply Primrec₂.mk
    refine Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) ?_
    apply Primrec₂.mk
    exact Primrec.list_map (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec₂.mk (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine (Primrec.nat_rec' Primrec.snd (Primrec.const [[]]) hstep).of_eq fun x => ?_
  exact (wordsOfLen_eq x.1 x.2).symm

private theorem wordsUpTo_primrec [Primcodable α] :
    Primrec (fun x : List α × ℕ => wordsUpTo x.1 x.2) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact wordsOfLen_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

private lemma mem_wordsOfLen (alphabet : List α) (n : ℕ) (w : List α) :
    w ∈ wordsOfLen alphabet n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero =>
      constructor
      · intro hw
        have hw' : w = [] := by simpa [wordsOfLen] using hw
        exact ⟨by simp [hw'], by simp [hw']⟩
      · rintro ⟨hlen, _⟩
        cases w with
        | nil => simp [wordsOfLen]
        | cons a w => simp at hlen
  | succ n ih =>
      constructor
      · intro hw
        rw [wordsOfLen, List.mem_flatMap] at hw
        rcases hw with ⟨v, hv, hwmap⟩
        rw [List.mem_map] at hwmap
        rcases hwmap with ⟨a, ha, rfl⟩
        have hv' := (ih v).mp hv
        constructor
        · simp [hv'.1]
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ha
          · exact hv'.2 b hb'
      · intro hw
        cases w with
        | nil =>
            simp at hw
        | cons a v =>
            rw [wordsOfLen, List.mem_flatMap]
            have hvlen : v.length = n := by
              exact Nat.succ.inj hw.1
            have hvmem : ∀ b ∈ v, b ∈ alphabet := by
              intro b hb
              exact hw.2 b (List.mem_cons_of_mem a hb)
            refine ⟨v, (ih v).mpr ⟨hvlen, hvmem⟩, ?_⟩
            exact List.mem_map.mpr ⟨a, hw.2 a (by simp), rfl⟩

private lemma mem_wordsUpTo_univ [Fintype α] [DecidableEq α] (n : ℕ) (w : List α) :
    w ∈ wordsUpTo ((Finset.univ : Finset α).toList) n ↔ w.length ≤ n := by
  rw [wordsUpTo, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hw⟩
    rw [List.mem_range] at hk
    have hw' := (mem_wordsOfLen ((Finset.univ : Finset α).toList) k w).mp hw
    omega
  · intro hwlen
    refine ⟨w.length, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · rw [mem_wordsOfLen]
      exact ⟨rfl, by intro a _; simp⟩

private def wordSearch (candidates : List (List α)) (p : List α → Bool) : Bool :=
  Nat.rec false (fun i acc => acc || p (candidates.getD i [])) candidates.length

private lemma wordSearch_rec_true_iff (candidates : List (List α)) (p : List α → Bool) :
    ∀ k : ℕ,
      Nat.rec false (fun i acc => acc || p (candidates.getD i [])) k = true ↔
        ∃ i, i < k ∧ p (candidates.getD i []) = true
  | 0 => by simp
  | k + 1 => by
      change
        (Nat.rec false (fun i acc => acc || p (candidates.getD i [])) k ||
            p (candidates.getD k [])) = true ↔
          ∃ i, i < k + 1 ∧ p (candidates.getD i []) = true
      rw [Bool.or_eq_true, wordSearch_rec_true_iff candidates p k]
      constructor
      · rintro (⟨i, hi, hp⟩ | hp)
        · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), hp⟩
        · exact ⟨k, Nat.lt_succ_self k, hp⟩
      · rintro ⟨i, hi, hp⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi' | rfl
        · exact Or.inl ⟨i, hi', hp⟩
        · exact Or.inr hp

private lemma wordSearch_true_iff_exists_mem (candidates : List (List α))
    (p : List α → Bool) :
    wordSearch candidates p = true ↔ ∃ w ∈ candidates, p w = true := by
  unfold wordSearch
  rw [wordSearch_rec_true_iff]
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨candidates.getD i [], ?_, hp⟩
    have hget : candidates[i]?.getD [] = candidates[i] := by
      simp [List.getElem?_eq_getElem hi]
    have hmem : candidates[i] ∈ candidates := List.getElem_mem hi
    simp [List.getD_eq_getElem?_getD, hget, hmem]
  · rintro ⟨w, hw, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    refine ⟨i, hi, ?_⟩
    have hget : candidates[i]?.getD [] = candidates[i] := by
      simp [List.getElem?_eq_getElem hi]
    simpa [List.getD_eq_getElem?_getD, hget] using hp

private theorem wordSearch_computable [Primcodable α] [Primcodable δ]
    {candidates : δ → List (List α)} {p : δ → List α → Bool}
    (hcandidates : Computable candidates) (hp : Computable₂ p) :
    Computable (fun d => wordSearch (candidates d) (p d)) := by
  unfold wordSearch
  have hstep : Computable₂ (fun d (q : ℕ × Bool) =>
      q.2 || p d ((candidates d).getD q.1 [])) := by
    apply Computable₂.mk
    have hword : Computable (fun q : δ × (ℕ × Bool) =>
        (candidates q.1).getD q.2.1 ([] : List α)) :=
      (Primrec.list_getD ([] : List α)).to_comp.comp
        (hcandidates.comp Computable.fst) (Computable.fst.comp Computable.snd)
    have hpred : Computable (fun q : δ × (ℕ × Bool) =>
        p q.1 ((candidates q.1).getD q.2.1 [])) :=
      hp.comp Computable.fst hword
    exact (Primrec.or.to_comp).comp (Computable.snd.comp Computable.snd) hpred
  exact Computable.nat_rec (Computable.list_length.comp hcandidates)
    (Computable.const false) hstep

private lemma mem_prod_singletons_iff_flatMap (w : List α) (h : α → List β) (u : List β) :
    u ∈ (w.map fun a => ({h a} : Language β)).prod ↔ u = w.flatMap h := by
  induction w generalizing u with
  | nil =>
      simp
  | cons a w ih =>
      constructor
      · intro hu
        rw [show (List.map (fun a => ({h a} : Language β)) (a :: w)).prod =
            ({h a} : Language β) * (List.map (fun a => ({h a} : Language β)) w).prod by rfl] at hu
        rw [Language.mem_mul] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₁' : u₁ = h a := by simpa using hu₁
        have hu₂' : u₂ = w.flatMap h := (ih u₂).mp hu₂
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun a => ({h a} : Language β)) (a :: w)).prod =
            ({h a} : Language β) * (List.map (fun a => ({h a} : Language β)) w).prod by rfl]
        rw [Language.mem_mul]
        exact ⟨h a, Set.mem_singleton _, w.flatMap h, (ih _).mpr rfl, rfl⟩

private lemma mem_homomorphicImage_iff_flatMap (L : Language α) (h : α → List β)
    (u : List β) :
    u ∈ L.homomorphicImage h ↔ ∃ w ∈ L, w.flatMap h = u := by
  simp only [Language.homomorphicImage, Language.subst]
  constructor
  · rintro ⟨w, hwL, hu⟩
    exact ⟨w, hwL, ((mem_prod_singletons_iff_flatMap w h u).mp hu).symm⟩
  · rintro ⟨w, hwL, rfl⟩
    exact ⟨w, hwL, (mem_prod_singletons_iff_flatMap w h _).mpr rfl⟩

private lemma length_le_flatMap_of_epsFree (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) (w : List α) :
    w.length ≤ (w.flatMap h).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha : 0 < (h a).length := List.length_pos_iff.mpr (heps a)
      calc
        (a :: w).length = w.length + 1 := by simp
        _ ≤ (w.flatMap h).length + (h a).length := by omega
        _ = (h a ++ w.flatMap h).length := by rw [List.length_append]; omega
        _ = ((a :: w).flatMap h).length := by simp [List.flatMap_cons]

private lemma length_le_of_flatMap_eq (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) {w : List α} {u : List β}
    (hwu : w.flatMap h = u) :
    w.length ≤ u.length := by
  simpa [hwu] using length_le_flatMap_of_epsFree h heps w

private noncomputable def epsFreeHomDecider [Fintype α] [DecidableEq β]
    (f : List α → Bool) (h : α → List β)
    (u : List β) : Bool :=
  wordSearch (wordsUpTo ((Finset.univ : Finset α).toList) u.length)
    (fun w => f w && decide (w.flatMap h = u))

private theorem epsFreeHomDecider_computable [Fintype α] [DecidableEq β]
    [Primcodable α] [Primcodable β]
    {f : List α → Bool} (hf : Computable f) (h : α → List β) :
    Computable (epsFreeHomDecider f h) := by
  classical
  unfold epsFreeHomDecider
  let alphabet : List α := (Finset.univ : Finset α).toList
  have hcandidates : Computable (fun u : List β => wordsUpTo alphabet u.length) :=
    wordsUpTo_primrec.to_comp.comp
      ((Computable.const alphabet).pair Computable.list_length)
  have hp : Computable₂ (fun (u : List β) (w : List α) =>
      f w && decide (w.flatMap h = u)) := by
    apply Computable₂.mk
    have heq : Computable (fun q : List β × List α => decide (q.2.flatMap h = q.1)) :=
      (computable₂_flatMap_eq_finite h).comp Computable.snd Computable.fst
    exact (Primrec.and.to_comp).comp (hf.comp Computable.snd) heq
  exact wordSearch_computable hcandidates hp

private lemma epsFreeHomDecider_true_iff [Fintype α] [DecidableEq α] [DecidableEq β]
    {L : Language α} {f : List α → Bool} {h : α → List β}
    (hmem : ∀ w : List α, w ∈ L ↔ f w = true)
    (heps : IsEpsFreeHomomorphism h) (u : List β) :
    epsFreeHomDecider f h u = true ↔ u ∈ L.homomorphicImage h := by
  rw [mem_homomorphicImage_iff_flatMap]
  unfold epsFreeHomDecider
  rw [wordSearch_true_iff_exists_mem]
  constructor
  · rintro ⟨w, hwlist, htest⟩
    rw [Bool.and_eq_true] at htest
    exact ⟨w, (hmem w).mpr htest.1, of_decide_eq_true htest.2⟩
  · rintro ⟨w, hwL, hwu⟩
    refine ⟨w, ?_, ?_⟩
    · rw [mem_wordsUpTo_univ]
      exact length_le_of_flatMap_eq h heps hwu
    · rw [Bool.and_eq_true]
      exact ⟨(hmem w).mp hwL, by simp [hwu]⟩

/-- Recursive languages over finite alphabets are closed under ε-free string homomorphism. -/
public theorem is_Recursive_epsFreeHomomorphism {α β : Type}
    [Fintype α] [Fintype β] (L : Language α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) :
    is_Recursive L → is_Recursive (L.homomorphicImage h) := by
  intro hL
  classical
  haveI : DecidableEq α := Classical.decEq _
  haveI : DecidableEq β := Classical.decEq _
  haveI : Primcodable α :=
    Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.truncEquivFin α).out
  haveI : Primcodable β :=
    Primcodable.ofEquiv (Fin (Fintype.card β)) (Fintype.truncEquivFin β).out
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hL)
  have hmem : ∀ w : List α, w ∈ L ↔ f w = true := fun w => by
    simpa using (iff_of_eq (congrFun hs w))
  refine is_Recursive_of_computable_decide (L.homomorphicImage h)
    (epsFreeHomDecider f h) (epsFreeHomDecider_computable hf h) ?_
  intro u
  exact (epsFreeHomDecider_true_iff hmem heps u).symm

/-- The class of recursive languages is closed under ε-free string homomorphism. -/
public theorem Recursive_closedUnderEpsFreeHomomorphism :
    ClosedUnderEpsFreeHomomorphism is_Recursive := by
  intro α β _ _ L h heps hL
  exact is_Recursive_epsFreeHomomorphism L h heps hL
