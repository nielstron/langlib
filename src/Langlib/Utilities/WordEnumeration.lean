module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

@[expose]
public section

/-!
# Enumerating Bounded Words

This file provides a small computable enumeration of all words up to a given
length over an explicitly supplied finite alphabet list, plus a reusable bounded
search combinator over such word lists.
-/

variable {α δ : Type}

/-- All words of exactly length `n` over the symbols in `alphabet`. -/
public def wordsOfLen (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => (wordsOfLen alphabet k).flatMap fun w => alphabet.map fun a => a :: w

/-- All words of length at most `n` over the symbols in `alphabet`. -/
public def wordsUpTo (alphabet : List α) (n : ℕ) : List (List α) :=
  (List.range (n + 1)).flatMap (wordsOfLen alphabet)

public theorem wordsOfLen_eq (alphabet : List α) (n : ℕ) :
    wordsOfLen alphabet n =
      Nat.rec (motive := fun _ => List (List α)) [[]]
        (fun _ ih => ih.flatMap fun w => alphabet.map fun a => a :: w) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [wordsOfLen, ih]

public theorem wordsOfLen_primrec [Primcodable α] :
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

public theorem wordsUpTo_primrec [Primcodable α] :
    Primrec (fun x : List α × ℕ => wordsUpTo x.1 x.2) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact wordsOfLen_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

public lemma mem_wordsOfLen (alphabet : List α) (n : ℕ) (w : List α) :
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
        | cons _ _ => simp at hlen
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

public lemma mem_wordsUpTo_univ [Fintype α] [DecidableEq α] (n : ℕ) (w : List α) :
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

/-- Search a finite candidate list for a word satisfying `p`. -/
public def wordSearch (candidates : List (List α)) (p : List α → Bool) : Bool :=
  Nat.rec false (fun i acc => acc || p (candidates.getD i [])) candidates.length

public lemma wordSearch_rec_true_iff (candidates : List (List α)) (p : List α → Bool) :
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

public lemma wordSearch_true_iff_exists_mem (candidates : List (List α))
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

public theorem wordSearch_computable [Primcodable α] [Primcodable δ]
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
