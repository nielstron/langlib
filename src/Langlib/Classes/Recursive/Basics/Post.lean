module

public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.Recursive.Inclusion.ByTapeFromComputable
public import Mathlib.Computability.Halting
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Grammars.Unrestricted.FiniteNonterminals
@[expose]
public section

/-! # Post's theorem for recursive languages

Post's theorem: a predicate whose positive and negative instances are both
recursively enumerable is computable; in language terms, a language that is RE and
co-RE is recursive. We package it both at the computability level
(`ComputablePred`) and at the recursive-language level (`is_Recursive`).

The bridge to `is_Recursive` goes through the tape-output decider construction
(`is_Recursive_of_computable_decide`): a `ComputablePred` membership yields a total
computable decider, which yields an always-halting TM0 decider.

## Main results

- `REPred_mem_of_is_RE` — membership in an RE language is an `REPred`.
- `computablePred_of_isRE_of_isRE_compl` — RE ∩ co-RE ⟹ computable membership.
- `is_Recursive_of_isRE_of_isRE_compl` — RE ∩ co-RE ⟹ recursive.
-/

variable {T : Type}

/-- For any recursively enumerable language over a `Primcodable` alphabet,
membership is a recursively enumerable predicate. This is the search over
derivation sequences made uniform via `grammarTest`. -/
public theorem REPred_mem_of_is_RE [DecidableEq T] [Primcodable T]
    {L : Language T} (hL : is_RE L) :
    REPred (fun w : List T => w ∈ L) := by
  obtain ⟨g, hg⟩ := hL
  obtain ⟨g', hfin, hlang⟩ := grammar_equivalent_finiteNT g
  haveI : Fintype g'.nt := Fintype.ofFinite _
  haveI : DecidableEq g'.nt := Classical.decEq _
  haveI : Primcodable g'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g'.nt)) (Fintype.truncEquivFin g'.nt).out
  have htest : Computable₂ (grammarTest g') := grammarTest_computable₂ g'
  have hpart : REPred (fun w : List T =>
      ∃ seq : List (ℕ × ℕ), grammarTest g' seq w = true) := by
    have hdom : Partrec (fun w : List T =>
        Nat.rfind (fun k =>
          Part.some (((Encodable.decode (α := List (ℕ × ℕ)) k).map
            (fun seq => grammarTest g' seq w)).getD false))) := by
      have hgEnc : Computable₂ (fun (w : List T) (k : ℕ) =>
          ((Encodable.decode (α := List (ℕ × ℕ)) k).map
            (fun seq => grammarTest g' seq w)).getD false) := by
        exact Computable.option_getD
          (Computable.option_map
            (Computable.decode.comp Computable.snd)
            (htest.comp
              (g := fun x : (List T × ℕ) × List (ℕ × ℕ) => x.2)
              (h := fun x : (List T × ℕ) × List (ℕ × ℕ) => x.1.1)
              Computable.snd
              (Computable.fst.comp Computable.fst)))
          (Computable.const false)
      exact Partrec.rfind hgEnc.partrec₂
    exact hdom.dom_re.of_eq fun w => by
      simp [Nat.rfind_dom]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨Denumerable.ofNat (List (ℕ × ℕ)) n, hn⟩
      · rintro ⟨seq, hseq⟩
        exact ⟨Encodable.encode seq, by simpa [Denumerable.ofNat_encode] using hseq⟩
  exact hpart.of_eq fun w => by
    constructor
    · rintro ⟨seq, hseq⟩
      have hmem : w ∈ grammar_language g' := grammarTest_sound g' seq w hseq
      rw [← hlang] at hmem
      rw [hg] at hmem
      exact hmem
    · intro h
      have hmem : w ∈ grammar_language g' := by
        rw [← hg] at h
        rw [hlang] at h
        exact h
      obtain ⟨seq, hseq⟩ := grammarTest_complete g' w hmem
      exact ⟨seq, hseq⟩

/-- **Post's theorem (RE ∩ co-RE = recursive), computability form.** A language that is
recursively enumerable and whose complement is recursively enumerable has computable
membership. -/
public theorem computablePred_of_isRE_of_isRE_compl [DecidableEq T] [Primcodable T]
    {L : Language T} (h1 : is_RE L) (h2 : is_RE Lᶜ) :
    ComputablePred (fun w : List T => w ∈ L) := by
  rw [ComputablePred.computable_iff_re_compl_re']
  refine ⟨REPred_mem_of_is_RE h1, ?_⟩
  exact (REPred_mem_of_is_RE h2).of_eq fun w => by rw [Set.mem_compl_iff]

/-- **Post's theorem, recursive form.** A language that is recursively enumerable and
whose complement is recursively enumerable is recursive (decided by an always-halting
TM0). -/
public theorem is_Recursive_of_isRE_of_isRE_compl
    [DecidableEq T] [Fintype T] [Primcodable T]
    {L : Language T} (h1 : is_RE L) (h2 : is_RE Lᶜ) : is_Recursive L := by
  obtain ⟨f, hf, hfe⟩ :=
    ComputablePred.computable_iff.mp (computablePred_of_isRE_of_isRE_compl h1 h2)
  exact is_Recursive_of_computable_decide L f hf
    (fun w => iff_of_eq (congrFun hfe w))
