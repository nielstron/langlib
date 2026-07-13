module

public import Langlib.Classes.Recursive.Basics.Post
import Langlib.Utilities.PrimrecHelpers
import Mathlib.Tactic

/-!
# Recursive Closure Under Kleene Star

This file proves that recursive languages are closed under Kleene star.

The decider builds a dynamic-programming table for the input word `w`.  The table
entry at index `j` records whether the prefix `w.take j` belongs to `L∗`; to fill
entry `j + 1`, it searches all earlier cut positions `i` and checks whether the
left prefix is already accepted and the nonempty block `w.drop i |>.take (j + 1 - i)`
belongs to `L`.
-/

variable {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]

private def starCellSearch (f : List T → Bool) (w : List T) (table : List Bool)
    (j : ℕ) (k : ℕ) : Bool :=
  Nat.rec false
    (fun i acc => acc || (table.getD i false && f ((w.drop i).take (j - i)))) k

private def starCell (f : List T → Bool) (w : List T) (table : List Bool) (j : ℕ) : Bool :=
  starCellSearch f w table j j

private def starTable (f : List T → Bool) (w : List T) (n : ℕ) : List Bool :=
  Nat.rec [true] (fun j table => table ++ [starCell f w table (j + 1)]) n

private def starDecider (f : List T → Bool) (w : List T) : Bool :=
  (starTable f w w.length).getD w.length false

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starCellSearch_rec_true_iff (f : List T → Bool) (w : List T)
    (table : List Bool) (j : ℕ) :
    ∀ k : ℕ,
      starCellSearch f w table j k = true ↔
        ∃ i, i < k ∧ table.getD i false = true ∧
          f ((w.drop i).take (j - i)) = true
  | 0 => by simp [starCellSearch]
  | k + 1 => by
      change
        (starCellSearch f w table j k ||
            (table.getD k false && f ((w.drop k).take (j - k)))) = true ↔
          ∃ i, i < k + 1 ∧ table.getD i false = true ∧
            f ((w.drop i).take (j - i)) = true
      rw [Bool.or_eq_true, Bool.and_eq_true, starCellSearch_rec_true_iff f w table j k]
      constructor
      · rintro (⟨i, hi, htab, hmem⟩ | ⟨htab, hmem⟩)
        · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), htab, hmem⟩
        · exact ⟨k, Nat.lt_succ_self k, htab, hmem⟩
      · rintro ⟨i, hi, htab, hmem⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi' | rfl
        · exact Or.inl ⟨i, hi', htab, hmem⟩
        · exact Or.inr ⟨htab, hmem⟩

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starCell_rec_true_iff (f : List T → Bool) (w : List T) (table : List Bool)
    (j : ℕ) :
    starCell f w table j = true ↔
      ∃ i, i < j ∧ table.getD i false = true ∧
        f ((w.drop i).take (j - i)) = true := by
  simpa [starCell] using starCellSearch_rec_true_iff f w table j j

omit [DecidableEq T] [Fintype T] in
private theorem starCell_computable {f : List T → Bool} (hf : Computable f) :
    Computable (fun ctx : List T × List Bool × ℕ => starCell f ctx.1 ctx.2.1 ctx.2.2) := by
  unfold starCell
  have hstep : Computable₂ (fun (ctx : List T × List Bool × ℕ) (p : ℕ × Bool) =>
      p.2 || (ctx.2.1.getD p.1 false && f ((ctx.1.drop p.1).take (ctx.2.2 - p.1)))) := by
    apply Computable₂.mk
    have hidx : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) => q.2.1) :=
      Computable.fst.comp Computable.snd
    have hword : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) => q.1.1) :=
      Computable.fst.comp Computable.fst
    have htable : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) => q.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hj : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) => q.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hacc : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have htab : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) =>
        q.1.2.1.getD q.2.1 false) :=
      (Primrec.list_getD false).to_comp.comp htable hidx
    have hdrop : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) =>
        q.1.1.drop q.2.1) :=
      (primrec₂_list_drop (α := T)).to_comp.comp hidx hword
    have hlen : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) =>
        q.1.2.2 - q.2.1) :=
      (Primrec.nat_sub.to_comp).comp hj hidx
    have hseg : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) =>
        (q.1.1.drop q.2.1).take (q.1.2.2 - q.2.1)) :=
      (primrec₂_list_take (α := T)).to_comp.comp hlen hdrop
    have hboth : Computable (fun q : (List T × List Bool × ℕ) × (ℕ × Bool) =>
        q.1.2.1.getD q.2.1 false && f ((q.1.1.drop q.2.1).take (q.1.2.2 - q.2.1))) :=
      (Primrec.and.to_comp).comp htab (hf.comp hseg)
    exact (Primrec.or.to_comp).comp hacc hboth
  exact Computable.nat_rec (Computable.snd.comp Computable.snd)
    (Computable.const false) hstep

omit [DecidableEq T] [Fintype T] in
private theorem starTable_computable {f : List T → Bool} (hf : Computable f) :
    Computable (fun w : List T => starTable f w w.length) := by
  unfold starTable
  have hstep : Computable₂ (fun (w : List T) (p : ℕ × List Bool) =>
      p.2 ++ [starCell f w p.2 (p.1 + 1)]) := by
    apply Computable₂.mk
    have hcell : Computable (fun q : List T × (ℕ × List Bool) =>
        starCell f q.1 q.2.2 (q.2.1 + 1)) :=
      (starCell_computable hf).comp
        (Computable.fst.pair
          ((Computable.snd.comp Computable.snd).pair
            (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    have hsingleton : Computable (fun q : List T × (ℕ × List Bool) =>
        [starCell f q.1 q.2.2 (q.2.1 + 1)]) :=
      (Primrec.list_cons.to_comp).comp hcell (Computable.const [])
    exact (Primrec.list_append.to_comp).comp
      (Computable.snd.comp Computable.snd) hsingleton
  exact Computable.nat_rec Computable.list_length (Computable.const [true]) hstep

omit [DecidableEq T] [Fintype T] in
private theorem starDecider_computable {f : List T → Bool} (hf : Computable f) :
    Computable (starDecider f) := by
  unfold starDecider
  exact (Primrec.list_getD false).to_comp.comp (starTable_computable hf) Computable.list_length

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma kstar_append_mem {L : Language T} {u v : List T}
    (hu : u ∈ KStar.kstar L) (hv : v ∈ L) :
    u ++ v ∈ KStar.kstar L := by
  rw [Language.mem_kstar] at hu ⊢
  rcases hu with ⟨S, rfl, hS⟩
  refine ⟨S ++ [v], by simp, ?_⟩
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact hS y hy
  · have hy_eq : y = v := by simpa using hy
    simpa [hy_eq] using hv

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma take_split_eq (w : List T) {i j : ℕ} (hij : i ≤ j) :
    w.take j = w.take i ++ (w.drop i).take (j - i) := by
  calc
    w.take j = (w.take j).take i ++ (w.take j).drop i :=
      (List.take_append_drop i (w.take j)).symm
    _ = w.take i ++ (w.drop i).take (j - i) := by
      simp [List.take_take, List.drop_take, Nat.min_eq_left hij]

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starCell_correct {L : Language T} {f : List T → Bool}
    (hmem : ∀ x : List T, x ∈ L ↔ f x = true)
    (w : List T) (table : List Bool) {j : ℕ}
    (hjpos : 0 < j) (hjle : j ≤ w.length)
    (htable : ∀ i, i < j → (table.getD i false = true ↔ w.take i ∈ KStar.kstar L)) :
    starCell f w table j = true ↔ w.take j ∈ KStar.kstar L := by
  rw [starCell_rec_true_iff]
  constructor
  · rintro ⟨i, hij, htab, hseg⟩
    have hprefix : w.take i ∈ KStar.kstar L := (htable i hij).mp htab
    have hblock : (w.drop i).take (j - i) ∈ L := (hmem _).mpr hseg
    have hsplit : w.take j = w.take i ++ (w.drop i).take (j - i) :=
      take_split_eq w hij.le
    rw [hsplit]
    exact kstar_append_mem hprefix hblock
  · intro hstar
    rw [Language.mem_kstar_iff_exists_nonempty] at hstar
    rcases hstar with ⟨S, hflat, hS⟩
    induction' S using List.reverseRecOn with S y ih
    · have : (w.take j).length = 0 := by simp [hflat]
      rw [List.length_take, Nat.min_eq_left hjle] at this
      omega
    · have hy : y ∈ L ∧ y ≠ [] := hS y (by simp)
      let i := S.flatten.length
      have hlen : j = i + y.length := by
        have h := congrArg List.length hflat
        simp [List.length_flatten, Nat.min_eq_left hjle] at h
        have hi : i = (List.map List.length S).sum := by
          simp [i, List.length_flatten]
        omega
      have hprefix : w.take i ∈ KStar.kstar L := by
        have hSi : S.flatten ∈ KStar.kstar L := by
          rw [Language.mem_kstar]
          exact ⟨S, rfl, fun z hz => (hS z (by simp [hz])).1⟩
        have htake : w.take i = S.flatten := by
          have htake' : (w.take j).take i = S.flatten := by
            simp [hflat, i]
          have hile : i ≤ j := by
            omega
          simpa [List.take_take, Nat.min_eq_left hile] using htake'
        simpa [htake] using hSi
      have hseg : (w.drop i).take (j - i) ∈ L := by
        have hdrop : (w.drop i).take (j - i) = y := by
          have hdrop' : (w.take j).drop i = y := by
            simp [hflat, i]
          simpa [List.drop_take] using hdrop'
        simpa [hdrop] using hy.1
      have hij : i < j := by
        have hypos : 0 < y.length := by
          cases y with
          | nil => exact (hy.2 rfl).elim
          | cons _ _ => simp
        omega
      exact ⟨i, hij, (htable i hij).mpr hprefix, (hmem _).mp hseg⟩

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starTable_length (f : List T → Bool) (w : List T) :
    ∀ n : ℕ, (starTable f w n).length = n + 1
  | 0 => by simp [starTable]
  | n + 1 => by
      change (starTable f w n ++ [starCell f w (starTable f w n) (n + 1)]).length =
        n + 1 + 1
      simp [starTable_length f w n, Nat.add_assoc]

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starTable_correct {L : Language T} {f : List T → Bool}
    (hmem : ∀ x : List T, x ∈ L ↔ f x = true) (w : List T) :
    ∀ n : ℕ, n ≤ w.length →
      ∀ j, j ≤ n →
        ((starTable f w n).getD j false = true ↔ w.take j ∈ KStar.kstar L)
  | 0, _hn, j, hj => by
      cases Nat.eq_zero_of_le_zero hj
      simp [starTable, Language.nil_mem_kstar]
  | n + 1, hn, j, hj => by
      rcases Nat.lt_or_eq_of_le hj with hjlt | rfl
      · have hjn : j ≤ n := Nat.lt_succ_iff.mp hjlt
        have hstable :
            (starTable f w (n + 1)).getD j false = (starTable f w n).getD j false := by
          change
            (starTable f w n ++ [starCell f w (starTable f w n) (n + 1)]).getD j false =
              (starTable f w n).getD j false
          rw [List.getD_append]
          simpa [starTable_length f w n] using hjlt
        rw [hstable]
        exact starTable_correct hmem w n (Nat.le_trans (Nat.le_succ n) hn) j hjn
      · have hnew :
            (starTable f w (n + 1)).getD (n + 1) false =
              starCell f w (starTable f w n) (n + 1) := by
          change
            (starTable f w n ++ [starCell f w (starTable f w n) (n + 1)]).getD (n + 1)
                false =
              starCell f w (starTable f w n) (n + 1)
          rw [List.getD_append_right]
          · simp [starTable_length f w n]
          · simp [starTable_length f w n]
        rw [hnew]
        exact starCell_correct hmem w (starTable f w n) (Nat.succ_pos n) hn
          (fun i hi => starTable_correct hmem w n (Nat.le_trans (Nat.le_succ n) hn) i
            (Nat.lt_succ_iff.mp hi))

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma starDecider_true_iff {L : Language T} {f : List T → Bool}
    (hmem : ∀ x : List T, x ∈ L ↔ f x = true) (w : List T) :
    starDecider f w = true ↔ w ∈ KStar.kstar L := by
  unfold starDecider
  simpa using starTable_correct hmem w w.length le_rfl w.length le_rfl

/-- Recursive languages over finite, primcodable alphabets are closed under Kleene star. -/
public theorem is_Recursive_star {L : Language T} (hL : is_Recursive L) :
    is_Recursive (KStar.kstar L) := by
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hL)
  have hmem : ∀ x : List T, x ∈ L ↔ f x = true := fun x => by
    simpa using (iff_of_eq (congrFun hs x))
  refine is_Recursive_of_computable_decide (KStar.kstar L) (starDecider f)
    (starDecider_computable hf) ?_
  intro w
  exact (starDecider_true_iff hmem w).symm

/-- The class of recursive languages is closed under Kleene star. -/
public theorem Recursive_closedUnderKleeneStar :
    ClosedUnderKleeneStar (α := T) is_Recursive :=
  fun _ hL => is_Recursive_star hL
