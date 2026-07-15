module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation
import Mathlib.Tactic

@[expose]
public section

/-!
# Finite reachability by inductive counting

This file isolates the finite-graph correctness argument behind the
Immerman--Szelepcsényi theorem.  For a finite directed graph, `reached edge source k`
is the set of vertices reachable in at most `k` steps.  It stabilizes after at most
`Fintype.card V` rounds and then agrees with reflexive-transitive reachability.

`Enumeration`, `Round`, `CertifiedCount`, and `Rejection` describe an inductive-counting
certificate for nonreachability.  Their `Finset` fields are mathematical transcripts of
canonical scans through `Finset.univ`; they need not be stored by an implementation.  A
space-bounded verifier can stream a scan while retaining only the current vertex, a path
certificate, and counters bounded by `Fintype.card V`.

The final correctness result is `nonreachable_iff_counting_certificate`.
-/

namespace FiniteReachabilityCounting

open Relation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (edge : V → V → Prop) [DecidableRel edge] (source : V)

/-- Add every one-step successor of a finite set. -/
def grow (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun v ↦ ∃ u ∈ S, edge u v

/-- Membership in `grow` is old membership or a one-step successor of an old vertex. -/
theorem mem_grow {S : Finset V} {v : V} :
    v ∈ grow edge S ↔ v ∈ S ∨ ∃ u ∈ S, edge u v := by
  simp [grow]

theorem subset_grow (S : Finset V) : S ⊆ grow edge S := by
  intro v hv
  exact (mem_grow edge).2 (Or.inl hv)

theorem grow_mono {S T : Finset V} (hST : S ⊆ T) :
    grow edge S ⊆ grow edge T := by
  intro v hv
  rw [mem_grow edge] at hv ⊢
  rcases hv with hv | ⟨u, hu, huv⟩
  · exact Or.inl (hST hv)
  · exact Or.inr ⟨u, hST hu, huv⟩

/-- The vertices reachable from `source` in at most `k` directed steps. -/
def reached : Nat → Finset V
  | 0 => {source}
  | k + 1 => grow edge (reached k)

@[simp] theorem reached_zero : reached edge source 0 = {source} := rfl

@[simp] theorem reached_succ (k : Nat) :
    reached edge source (k + 1) = grow edge (reached edge source k) := rfl

theorem reached_mono (k : Nat) :
    reached edge source k ⊆ reached edge source (k + 1) := by
  rw [reached_succ]
  exact subset_grow edge _

theorem reached_mono_nat {i j : Nat} (hij : i ≤ j) :
    reached edge source i ⊆ reached edge source j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih => exact ih.trans (reached_mono edge source j)

/-- An exactly fuel-indexed path in the reflexive closure of `edge`.  Stuttering
allows a path of at most `k` genuine edges to be padded to exactly `k` verifier
steps without changing its endpoint. -/
inductive PaddedPath : Nat → V → Prop
  | zero : PaddedPath 0 source
  | succ {k : Nat} {old new : V} :
      PaddedPath k old → (old = new ∨ edge old new) → PaddedPath (k + 1) new

/-- Bounded reachability is exactly existence of a fuel-indexed padded path. -/
theorem mem_reached_iff_paddedPath {k : Nat} {v : V} :
    v ∈ reached edge source k ↔ PaddedPath edge source k v := by
  induction k generalizing v with
  | zero =>
      constructor
      · intro hv
        have : v = source := by simpa [reached] using hv
        subst v
        exact .zero
      · intro h
        cases h
        simp [reached]
  | succ k ih =>
      rw [reached_succ, mem_grow]
      constructor
      · rintro (hv | ⟨u, hu, huv⟩)
        · exact .succ (ih.mp hv) (Or.inl rfl)
        · exact .succ (ih.mp hu) (Or.inr huv)
      · intro h
        cases h with
        | succ hpath hstep =>
            rcases hstep with rfl | hedge
            · exact Or.inl (ih.mpr hpath)
            · exact Or.inr ⟨_, ih.mpr hpath, hedge⟩

/-- Every bounded-reachable vertex is reachable in the ordinary relational sense. -/
theorem reached_sound {k : Nat} {v : V} (hv : v ∈ reached edge source k) :
    ReflTransGen edge source v := by
  induction k generalizing v with
  | zero =>
      have hvs : v = source := by simpa [reached] using hv
      subst v
      exact .refl
  | succ k ih =>
      rw [reached_succ, mem_grow] at hv
      rcases hv with hv | ⟨u, hu, huv⟩
      · exact ih hv
      · exact (ih hu).tail huv

/-- Once a reachability round adds no vertex, every later round is identical. -/
theorem reached_eq_of_plateau {k : Nat}
    (h : reached edge source k = reached edge source (k + 1)) (m : Nat) :
    reached edge source (k + m) = reached edge source k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, reached_succ, ih]
      simpa [reached_succ] using h.symm

/-- If round `n` has not stabilized, no earlier round has stabilized. -/
theorem no_earlier_plateau {n k : Nat} (hkn : k ≤ n)
    (hn : reached edge source n ≠ reached edge source (n + 1)) :
    reached edge source k ≠ reached edge source (k + 1) := by
  intro hk
  have hs := reached_eq_of_plateau edge source hk (n - k)
  have hs' := reached_eq_of_plateau edge source hk (n + 1 - k)
  have hnk : k + (n - k) = n := Nat.add_sub_of_le hkn
  have hnk' : k + (n + 1 - k) = n + 1 :=
    Nat.add_sub_of_le (hkn.trans (Nat.le_succ n))
  apply hn
  calc
    reached edge source n = reached edge source k := by rw [← hnk]; exact hs
    _ = reached edge source (n + 1) := by rw [← hnk']; exact hs'.symm

theorem card_reached_lower_of_nonplateau {n : Nat}
    (hn : reached edge source n ≠ reached edge source (n + 1)) :
    n + 1 ≤ (reached edge source n).card := by
  induction n with
  | zero => simp [reached]
  | succ n ih =>
      have hn' : reached edge source n ≠ reached edge source (n + 1) :=
        no_earlier_plateau edge source (Nat.le_succ n) hn
      have hss : reached edge source n ⊂ reached edge source (n + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨reached_mono edge source n, hn'⟩
      have hcard := Finset.card_lt_card hss
      have hlower := ih hn'
      omega

/-- Finite reachability has stabilized after `Fintype.card V` rounds. -/
theorem reached_card_fixed :
    reached edge source (Fintype.card V) =
      reached edge source (Fintype.card V + 1) := by
  by_contra h
  have hlower := card_reached_lower_of_nonplateau edge source h
  have hupper := Finset.card_le_univ (reached edge source (Fintype.card V))
  omega

/-- Saturated bounded reachability is exactly reflexive-transitive reachability. -/
theorem mem_reached_card_iff {v : V} :
    v ∈ reached edge source (Fintype.card V) ↔ ReflTransGen edge source v := by
  constructor
  · exact reached_sound edge source
  · intro h
    have hs : source ∈ reached edge source (Fintype.card V) :=
      reached_mono_nat edge source (Nat.zero_le _) (by simp [reached])
    have hclosed : ∀ {u v : V}, u ∈ reached edge source (Fintype.card V) →
        edge u v → v ∈ reached edge source (Fintype.card V) := by
      intro u v hu huv
      have hv : v ∈ reached edge source (Fintype.card V + 1) := by
        rw [reached_succ, mem_grow]
        exact Or.inr ⟨u, hu, huv⟩
      rwa [← reached_card_fixed edge source] at hv
    induction h with
    | refl => exact hs
    | tail _ huv ih => exact hclosed ih huv

/-- A transcript of vertices for which a canonical scan guessed reachability witnesses.

The fixed scan order means an implementation does not need a duplicate table. -/
structure Enumeration (k c : Nat) where
  vertices : Finset V
  card_eq : vertices.card = c
  sound : ∀ {v : V}, v ∈ vertices → v ∈ reached edge source k

/-- A sound enumeration of the exact expected cardinality contains every reachable vertex. -/
theorem Enumeration.eq_reached {k c : Nat}
    (hc : c = (reached edge source k).card)
    (E : Enumeration edge source k c) :
    E.vertices = reached edge source k := by
  apply Finset.eq_of_subset_of_card_le (fun _ hv ↦ E.sound hv)
  rw [E.card_eq, hc]

/-- One complete inductive-counting round.

`old` records successful old-reachability guesses.  `new` records the vertices declared
reachable in the next round; `positive` and `negative` validate both outcomes of the scan. -/
structure Round (k c d : Nat) where
  old : Enumeration edge source k c
  new : Finset V
  new_card : new.card = d
  positive : ∀ {v : V}, v ∈ new →
    v ∈ old.vertices ∨ ∃ u ∈ old.vertices, edge u v
  negative : ∀ {v : V}, v ∉ new →
    v ∉ old.vertices ∧ ∀ u ∈ old.vertices, ¬ edge u v

/-- If the input count to a round is exact, so is its output count. -/
theorem Round.correct {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) :
    d = (reached edge source (k + 1)).card := by
  have hold := Enumeration.eq_reached (edge := edge) (source := source) hc R.old
  have hnew : R.new = reached edge source (k + 1) := by
    ext v
    rw [reached_succ, mem_grow]
    constructor
    · intro hv
      simpa only [hold] using R.positive hv
    · intro hv
      by_contra hvn
      have hneg := R.negative hvn
      rw [hold] at hneg
      rcases hv with hv | ⟨u, hu, huv⟩
      · exact hneg.1 hv
      · exact hneg.2 u hu huv
  rw [← R.new_card, hnew]

/-- If an exact counting round leaves the count unchanged, bounded reachability has reached a
fixed point.  This is the plateau test used by the streaming Immerman--Szelepcsényi verifier. -/
theorem Round.reached_eq_succ_of_count_eq {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) (hdc : d = c) :
    reached edge source k = reached edge source (k + 1) := by
  apply Finset.eq_of_subset_of_card_le (reached_mono edge source k)
  rw [← R.correct (edge := edge) (source := source) hc, hdc, hc]

/-- After a count plateau, every later bounded-reachability layer is the same layer. -/
theorem Round.reached_eq_add_of_count_eq {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) (hdc : d = c) (m : Nat) :
    reached edge source (k + m) = reached edge source k :=
  reached_eq_of_plateau edge source
    (R.reached_eq_succ_of_count_eq (edge := edge) (source := source) hc hdc) m

/-- A plateau layer is the full reflexive-transitive reachable set, not merely a bounded
approximation. -/
theorem Round.mem_reached_iff_of_count_eq {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) (hdc : d = c) {v : V} :
    v ∈ reached edge source k ↔ ReflTransGen edge source v := by
  let layer := reached edge source k
  have hplateau := R.reached_eq_succ_of_count_eq
    (edge := edge) (source := source) hc hdc
  have hsource : source ∈ layer := by
    apply reached_mono_nat edge source (Nat.zero_le k)
    simp [reached]
  have hclosed : ∀ {u v : V}, u ∈ layer → edge u v → v ∈ layer := by
    intro u v hu huv
    have hv : v ∈ reached edge source (k + 1) := by
      rw [reached_succ, mem_grow]
      exact Or.inr ⟨u, hu, huv⟩
    rwa [← hplateau] at hv
  constructor
  · exact reached_sound edge source
  · intro hreach
    induction hreach with
    | refl => exact hsource
    | tail _ huv ih => exact hclosed ih huv

/-- A non-plateau exact round strictly increases the reachable count. -/
theorem Round.count_lt_of_ne {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) (hne : d ≠ c) :
    c < d := by
  have hsubset := reached_mono edge source k
  have hcard : (reached edge source k).card ≤
      (reached edge source (k + 1)).card := Finset.card_le_card hsubset
  have hd := R.correct (edge := edge) (source := source) hc
  omega

/-- A non-plateau round occurs before the number of vertices.  Thus a width-`n` row counter
needs only enough values for the `|V|` possible strict-growth rounds. -/
theorem Round.depth_lt_card_of_ne {k c d : Nat}
    (hc : c = (reached edge source k).card)
    (R : Round edge source k c d) (hne : d ≠ c) :
    k < Fintype.card V := by
  have hnonplateau : reached edge source k ≠ reached edge source (k + 1) := by
    intro heq
    apply hne
    have hd := R.correct (edge := edge) (source := source) hc
    calc
      d = (reached edge source (k + 1)).card := hd
      _ = (reached edge source k).card := congrArg Finset.card heq.symm
      _ = c := hc.symm
  have hlower := card_reached_lower_of_nonplateau edge source hnonplateau
  have hupper := Finset.card_le_univ (reached edge source k)
  omega

/-- A sequence of locally verified counting rounds, starting with the singleton source. -/
inductive CertifiedCount : Nat → Nat → Prop
  | zero : CertifiedCount 0 1
  | succ {k c d} : CertifiedCount k c → Round edge source k c d →
      CertifiedCount (k + 1) d

/-- Every certified count is the true bounded-reachability count. -/
theorem certifiedCount_sound {k c : Nat}
    (h : CertifiedCount edge source k c) :
    c = (reached edge source k).card := by
  induction h with
  | zero => simp [reached]
  | succ h R ih => exact Round.correct (edge := edge) (source := source) ih R

/-- The canonical transcript enumerating exactly the bounded-reachable vertices. -/
def canonicalEnumeration (k : Nat) :
    Enumeration edge source k (reached edge source k).card where
  vertices := reached edge source k
  card_eq := rfl
  sound := fun h ↦ h

/-- The canonical transcript for one counting round. -/
def canonicalRound (k : Nat) :
    Round edge source k (reached edge source k).card
      (reached edge source (k + 1)).card where
  old := canonicalEnumeration edge source k
  new := reached edge source (k + 1)
  new_card := rfl
  positive := by
    intro v hv
    change v ∈ reached edge source k ∨ ∃ u ∈ reached edge source k, edge u v
    exact (mem_grow edge).1 (by simpa [reached_succ] using hv)
  negative := by
    intro v hv
    rw [reached_succ, mem_grow] at hv
    push_neg at hv
    exact hv

/-- Exact bounded-reachability counts always have a certificate. -/
theorem certifiedCount_complete (k : Nat) :
    CertifiedCount edge source k (reached edge source k).card := by
  induction k with
  | zero =>
      simpa [reached] using CertifiedCount.zero (edge := edge) (source := source)
  | succ k ih => exact CertifiedCount.succ ih (canonicalRound edge source k)

/-- Certified counts are precisely the true bounded-reachability counts. -/
theorem certifiedCount_iff {k c : Nat} :
    CertifiedCount edge source k c ↔ c = (reached edge source k).card := by
  constructor
  · exact certifiedCount_sound edge source
  · rintro rfl
    exact certifiedCount_complete edge source k

/-- A final scan transcript claiming that `target` is absent. -/
structure Rejection (k c : Nat) (target : V) where
  seen : Enumeration edge source k c
  target_absent : target ∉ seen.vertices

/-- A rejection backed by the exact count proves bounded nonreachability. -/
theorem Rejection.correct {k c : Nat} {target : V}
    (hc : c = (reached edge source k).card)
    (R : Rejection edge source k c target) :
    target ∉ reached edge source k := by
  rw [← Enumeration.eq_reached (edge := edge) (source := source) hc R.seen]
  exact R.target_absent

/-- The canonical rejection transcript for an absent target. -/
def canonicalRejection {k : Nat} {target : V}
    (h : target ∉ reached edge source k) :
    Rejection edge source k (reached edge source k).card target where
  seen := canonicalEnumeration edge source k
  target_absent := h

/-- A final scan transcript claiming that every bounded-reachable vertex is nonfinal. -/
structure FinalRejection (k c : Nat) (final : V → Prop) where
  seen : Enumeration edge source k c
  all_nonfinal : ∀ {v : V}, v ∈ seen.vertices → ¬ final v

/-- A final rejection backed by the exact count excludes every reachable final vertex. -/
theorem FinalRejection.correct {k c : Nat} {final : V → Prop}
    (hc : c = (reached edge source k).card)
    (R : FinalRejection edge source k c final) :
    ∀ {v : V}, v ∈ reached edge source k → ¬ final v := by
  intro v hv
  apply R.all_nonfinal
  rwa [Enumeration.eq_reached (edge := edge) (source := source) hc R.seen]

/-- The canonical final rejection transcript. -/
def canonicalFinalRejection {k : Nat} {final : V → Prop}
    (h : ∀ {v : V}, v ∈ reached edge source k → ¬ final v) :
    FinalRejection edge source k (reached edge source k).card final where
  seen := canonicalEnumeration edge source k
  all_nonfinal := h

/-- Abstract Immerman--Szelepcsényi correctness for a finite directed graph:
nonreachability is equivalent to certified inductive counts followed by a rejecting scan. -/
theorem nonreachable_iff_counting_certificate {target : V} :
    ¬ ReflTransGen edge source target ↔
      ∃ c,
        CertifiedCount edge source (Fintype.card V) c ∧
        Nonempty (Rejection edge source (Fintype.card V) c target) := by
  rw [← mem_reached_card_iff edge source]
  constructor
  · intro h
    refine ⟨_, certifiedCount_complete edge source _,
      ⟨canonicalRejection edge source h⟩⟩
  · rintro ⟨c, hc, ⟨R⟩⟩
    exact Rejection.correct (edge := edge) (source := source)
      (certifiedCount_sound edge source hc) R

/-- No final vertex is reachable exactly when inductive counting can finish with a scan
certifying that every reachable vertex is nonfinal. -/
theorem no_reachable_final_iff_counting_certificate {final : V → Prop} :
    (¬ ∃ v, ReflTransGen edge source v ∧ final v) ↔
      ∃ c,
        CertifiedCount edge source (Fintype.card V) c ∧
        Nonempty (FinalRejection edge source (Fintype.card V) c final) := by
  constructor
  · intro h
    have hfinal : ∀ {v : V}, v ∈ reached edge source (Fintype.card V) →
        ¬ final v := by
      intro v hv hfv
      exact h ⟨v, (mem_reached_card_iff edge source).1 hv, hfv⟩
    exact ⟨_, certifiedCount_complete edge source _,
      ⟨canonicalFinalRejection edge source hfinal⟩⟩
  · rintro ⟨c, hc, ⟨R⟩⟩ ⟨v, hv, hfinal⟩
    exact FinalRejection.correct (edge := edge) (source := source)
      (certifiedCount_sound edge source hc) R
      ((mem_reached_card_iff edge source).2 hv) hfinal

/-- **Finite-graph Immerman--Szelepcsényi theorem.**  For every finite directed
graph, source vertex, and final predicate, absence of a reachable final vertex is
equivalent to an inductive-counting certificate followed by an exhaustive rejecting
scan.  No automaton model or particular vertex type is built into the statement. -/
public theorem immerman_szelepcsenyi {final : V → Prop} :
    (¬ ∃ v, ReflTransGen edge source v ∧ final v) ↔
      ∃ c,
        CertifiedCount edge source (Fintype.card V) c ∧
        Nonempty (FinalRejection edge source (Fintype.card V) c final) :=
  no_reachable_final_iff_counting_certificate edge source

end FiniteReachabilityCounting
