module

public import Langlib.Classes.Recursive.Decidability.Membership
import Langlib.Utilities.PrimrecHelpers

/-!
# Recursive Closure Under Concatenation

This file proves that recursive languages are closed under concatenation.

The decider searches the finitely many splits of the input word.  At split `n`, it checks
membership of `w.take n` in the left language and `w.drop n` in the right language.
-/

variable {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]

private def concatDecider (f₁ f₂ : List T → Bool) (w : List T) : Bool :=
  Nat.rec false (fun n acc => acc || (f₁ (w.take n) && f₂ (w.drop n))) (w.length + 1)

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma concatDecider_rec_true_iff (f₁ f₂ : List T → Bool) (w : List T) :
    ∀ k : ℕ,
      Nat.rec false (fun n acc => acc || (f₁ (w.take n) && f₂ (w.drop n))) k = true ↔
        ∃ n, n < k ∧ f₁ (w.take n) = true ∧ f₂ (w.drop n) = true
  | 0 => by simp
  | k + 1 => by
      change
        (Nat.rec false (fun n acc => acc || (f₁ (w.take n) && f₂ (w.drop n))) k ||
            (f₁ (w.take k) && f₂ (w.drop k))) = true ↔
          ∃ n, n < k + 1 ∧ f₁ (w.take n) = true ∧ f₂ (w.drop n) = true
      rw [Bool.or_eq_true, Bool.and_eq_true, concatDecider_rec_true_iff f₁ f₂ w k]
      constructor
      · rintro (⟨n, hn, h₁, h₂⟩ | ⟨h₁, h₂⟩)
        · exact ⟨n, Nat.lt_trans hn (Nat.lt_succ_self k), h₁, h₂⟩
        · exact ⟨k, Nat.lt_succ_self k, h₁, h₂⟩
      · rintro ⟨n, hn, h₁, h₂⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hn) with hn' | rfl
        · exact Or.inl ⟨n, hn', h₁, h₂⟩
        · exact Or.inr ⟨h₁, h₂⟩

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma concatDecider_true_iff (f₁ f₂ : List T → Bool) (w : List T) :
    concatDecider f₁ f₂ w = true ↔
      ∃ n, n < w.length + 1 ∧ f₁ (w.take n) = true ∧ f₂ (w.drop n) = true := by
  exact concatDecider_rec_true_iff f₁ f₂ w (w.length + 1)

omit [DecidableEq T] [Fintype T] in
private theorem concatDecider_computable {f₁ f₂ : List T → Bool}
    (hf₁ : Computable f₁) (hf₂ : Computable f₂) :
    Computable (concatDecider f₁ f₂) := by
  unfold concatDecider
  have hstep : Computable₂ (fun (w : List T) (p : ℕ × Bool) =>
      p.2 || (f₁ (w.take p.1) && f₂ (w.drop p.1))) := by
    apply Computable₂.mk
    have htake : Computable (fun p : List T × (ℕ × Bool) => p.1.take p.2.1) :=
      (primrec₂_list_take (α := T)).to_comp.comp
        (Computable.fst.comp Computable.snd) Computable.fst
    have hdrop : Computable (fun p : List T × (ℕ × Bool) => p.1.drop p.2.1) :=
      (primrec₂_list_drop (α := T)).to_comp.comp
        (Computable.fst.comp Computable.snd) Computable.fst
    have hboth : Computable (fun p : List T × (ℕ × Bool) =>
        f₁ (p.1.take p.2.1) && f₂ (p.1.drop p.2.1)) :=
      (Primrec.and.to_comp).comp (hf₁.comp htake) (hf₂.comp hdrop)
    exact (Primrec.or.to_comp).comp
      (Computable.snd.comp Computable.snd) hboth
  exact Computable.nat_rec (Computable.succ.comp Computable.list_length)
    (Computable.const false) hstep

omit [DecidableEq T] [Fintype T] [Primcodable T] in
private lemma mem_mul_iff_exists_take_drop (L₁ L₂ : Language T) (w : List T) :
    w ∈ L₁ * L₂ ↔
      ∃ n, n < w.length + 1 ∧ w.take n ∈ L₁ ∧ w.drop n ∈ L₂ := by
  constructor
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨u, hu, v, hv, huv⟩
    refine ⟨u.length, ?_, ?_, ?_⟩
    · rw [← huv, List.length_append]
      exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    · simpa [← huv] using hu
    · simpa [← huv] using hv
  · rintro ⟨n, _hn, htake, hdrop⟩
    rw [Language.mem_mul]
    exact ⟨w.take n, htake, w.drop n, hdrop, List.take_append_drop n w⟩

/-- Recursive languages over finite, primcodable alphabets are closed under concatenation. -/
public theorem is_Recursive_concatenation {L₁ L₂ : Language T}
    (h₁ : is_Recursive L₁) (h₂ : is_Recursive L₂) :
    is_Recursive (L₁ * L₂) := by
  obtain ⟨f₁, hf₁, hs₁⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable h₁)
  obtain ⟨f₂, hf₂, hs₂⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable h₂)
  refine is_Recursive_of_computable_decide (L₁ * L₂) (concatDecider f₁ f₂)
    (concatDecider_computable hf₁ hf₂) ?_
  intro w
  have hmem₁ : ∀ x : List T, x ∈ L₁ ↔ f₁ x = true := fun x => by
    simpa using (iff_of_eq (congrFun hs₁ x))
  have hmem₂ : ∀ x : List T, x ∈ L₂ ↔ f₂ x = true := fun x => by
    simpa using (iff_of_eq (congrFun hs₂ x))
  rw [mem_mul_iff_exists_take_drop, concatDecider_true_iff]
  constructor
  · rintro ⟨n, hn, hleft, hright⟩
    exact ⟨n, hn, (hmem₁ _).mp hleft, (hmem₂ _).mp hright⟩
  · rintro ⟨n, hn, hleft, hright⟩
    exact ⟨n, hn, (hmem₁ _).mpr hleft, (hmem₂ _).mpr hright⟩

/-- The class of recursive languages is closed under concatenation. -/
public theorem Recursive_closedUnderConcatenation :
    ClosedUnderConcatenation (α := T) is_Recursive :=
  fun _ _ h₁ h₂ => is_Recursive_concatenation h₁ h₂
