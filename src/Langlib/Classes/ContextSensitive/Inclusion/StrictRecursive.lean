module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextSensitive.Inclusion.Recursive
public import Langlib.Classes.ContextSensitive.Decidability.Membership
public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.Recursive.Inclusion.ByTapeFromComputable
public import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
public import Langlib.Classes.RecursivelyEnumerable.Basics.Lifting
public import Langlib.Grammars.Unrestricted.FiniteNonterminals
public import Mathlib.Computability.Halting
import Mathlib.Data.Fintype.BigOperators
@[expose]
public section



/-! # Strict Inclusion: CS ⊊ Recursive

Context-sensitive languages form a *strict* subclass of the recursive languages.

Unlike `Recursive ⊊ RE` (which follows from a closure asymmetry — Recursive is closed
under complement, RE is not), there is **no** standard closure property separating CS from
Recursive: both are closed under union, intersection, complement, concatenation, star,
reverse, ε-free homomorphism, … and both fail erasing homomorphism. So strictness here
requires a genuine **diagonalization**.

## Structure of the argument

`diagonal_strict` is the abstract core, proven here in full. We index the enumeration by
*words* (the diagonal then pairs each word-code with itself, avoiding any need for a separate
word↔ℕ bijection). Given

- an enumeration `e : List T → Language T` whose range covers every context-sensitive
  language (`hsurj`);
- a `Bool`-valued membership oracle `mem : List T → List T → Bool` that is **computable**
  (`hmem_comp`) and correct (`hmem`),

it builds the diagonal language `D = { v | mem v v = false }` and shows `D` is recursive (its
characteristic function is computable, via the `is_Recursive_of_computable_decide` bridge) but
not context-sensitive (the fixed-point contradiction `u ∈ D ↔ u ∉ e u`), hence
`CS ⊊ Recursive`.

## The enumeration

`exists_cs_enumeration` provides the effective enumeration: context-sensitive grammars are
coded with nonterminals in `ℕ` (`Code T`, `Primcodable`), decoded from a word by its length,
and membership is decided by a bounded search over derivation sequences (`memCode`). The decider
is uniformly computable (`memOracle_computable`, via the uniform `primrec_applyRuleSeq_uniform`),
sound (`memCode_sound`), complete within the bound for context-sensitive grammars
(`memCode_complete`, a minimal-witness + form-counting argument), and the coding covers every
context-sensitive language (`code_of_CS`, by relabelling nonterminals to `ℕ`).
-/

open Language

variable {T : Type}

/-- **Abstract diagonalization core (proven).** From a correct, computable membership oracle
for a word-indexed enumeration covering all context-sensitive languages, the diagonal language
is recursive but not context-sensitive, giving `CS ⊊ Recursive`. -/
public theorem diagonal_strict
    [DecidableEq T] [Fintype T] [Primcodable T]
    (e : List T → Language T)
    (mem : List T → List T → Bool)
    (hmem : ∀ u v, mem u v = true ↔ v ∈ e u)
    (hmem_comp : Computable (fun p : List T × List T => mem p.1 p.2))
    (hsurj : ∀ L : Language T, is_CS L → ∃ u, e u = L) :
    (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) := by
  classical
  -- Diagonal decider: accept `v` iff `v ∉ e v`.
  set f : List T → Bool := fun v => cond (mem v v) false true with hf_def
  set D : Language T := {v | f v = true} with hD_def
  -- `f` is computable: feed `mem` the diagonal pair `(v, v)`.
  have h1 : Computable (fun v : List T => mem v v) :=
    hmem_comp.comp (Computable.pair Computable.id Computable.id)
  have hf_comp : Computable f :=
    Computable.cond h1 (Computable.const false) (Computable.const true)
  -- `D` is recursive.
  have hDrec : is_Recursive D :=
    is_Recursive_of_computable_decide D f hf_comp (fun _ => Iff.rfl)
  -- `D` is not context-sensitive: a fixed-point contradiction.
  have hDnotCS : ¬ is_CS D := by
    rintro hCS
    obtain ⟨u, hu⟩ := hsurj D hCS
    have hfu : f u = cond (mem u u) false true := by rw [hf_def]
    have key : u ∈ D ↔ u ∉ e u := by
      rw [hD_def, Set.mem_setOf_eq, hfu, ← hmem u u]
      cases mem u u <;> simp
    rw [hu] at key
    exact iff_not_self key
  -- Assemble strict inclusion: ⊆ holds, and equality would put the non-CS recursive `D` in CS.
  refine ssubset_iff_subset_ne.mpr ⟨CS_subset_Recursive_class, ?_⟩
  intro heq
  exact hDnotCS ((Set.ext_iff.mp heq D).mpr hDrec)

/-! ## Uniform computability of `applyRuleSeq`

The project's `computable_applyRuleSeq` proves `applyRuleSeq rules init` computable for a
*fixed* rule list. For the enumeration we need it uniform in the rules (the grammar is runtime
data). We re-derive the `Primrec` facts threading `rules`/`init` as projections rather than
constants, reusing the uniform building blocks `primrec_applyRuleAt`. -/

/-- The single foldl step of `applyRuleSeq`, as an `Option.bind`, uniform in the rule list. -/
private theorem applyRuleSeq_step_eq_bind {N : Type} [DecidableEq T] [DecidableEq N]
    (q : (List (grule T N) × List (symbol T N) × List (ℕ × ℕ)) ×
         (Option (List (symbol T N)) × (ℕ × ℕ))) :
    (match q.2.1 with
      | none => none
      | some sf =>
        match q.1.1[q.2.2.1]? with
        | none => none
        | some r => applyRuleAt r sf q.2.2.2) =
    q.2.1.bind (fun sf => (q.1.1[q.2.2.1]?).bind (fun r => applyRuleAt r sf q.2.2.2)) := by
  cases q.2.1 <;> simp [Option.bind]
  rename_i sf
  cases q.1.1[q.2.2.1]? <;> simp [Option.bind]

/-- `applyRuleSeq` is primitive recursive uniformly in the rule list, initial form, and
derivation sequence. -/
public theorem primrec_applyRuleSeq_uniform {N : Type} [DecidableEq T] [DecidableEq N]
    [Primcodable T] [Primcodable N] :
    Primrec (fun p : List (grule T N) × List (symbol T N) × List (ℕ × ℕ) =>
      applyRuleSeq p.1 p.2.1 p.2.2) := by
  have hstep : Primrec (fun q : (List (grule T N) × List (symbol T N) × List (ℕ × ℕ)) ×
        (Option (List (symbol T N)) × (ℕ × ℕ)) =>
      match q.2.1 with
      | none => none
      | some sf =>
        match q.1.1[q.2.2.1]? with
        | none => none
        | some r => applyRuleAt r sf q.2.2.2) := by
    have hbind : Primrec (fun q : (List (grule T N) × List (symbol T N) × List (ℕ × ℕ)) ×
          (Option (List (symbol T N)) × (ℕ × ℕ)) =>
        q.2.1.bind (fun sf => (q.1.1[q.2.2.1]?).bind (fun r => applyRuleAt r sf q.2.2.2))) := by
      apply Primrec.option_bind
      · exact Primrec.fst.comp Primrec.snd
      -- inner: `Primrec₂ (fun q sf => (q.1.1[q.2.2.1]?).bind (fun r => applyRuleAt r sf q.2.2.2))`
      · have hidx : Primrec (fun w : ((List (grule T N) × List (symbol T N) × List (ℕ × ℕ)) ×
              (Option (List (symbol T N)) × (ℕ × ℕ))) × List (symbol T N) =>
            w.1.1.1[w.1.2.2.1]?) :=
          Primrec.list_getElem?.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        have happ : Primrec (fun x : (((List (grule T N) × List (symbol T N) × List (ℕ × ℕ)) ×
              (Option (List (symbol T N)) × (ℕ × ℕ))) × List (symbol T N)) × grule T N =>
            applyRuleAt x.2 x.1.2 x.1.1.2.2.2) :=
          primrec_applyRuleAt.comp
            (Primrec.pair Primrec.snd
              (Primrec.pair (Primrec.snd.comp Primrec.fst)
                (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))
        exact Primrec.option_bind hidx happ
    exact hbind.of_eq fun q => (applyRuleSeq_step_eq_bind q).symm
  have := Primrec.list_foldl
    (f := fun p : List (grule T N) × List (symbol T N) × List (ℕ × ℕ) => p.2.2)
    (g := fun p => (some p.2.1 : Option (List (symbol T N))))
    (h := fun p q => match q.1 with
      | none => none
      | some sf =>
        match p.1[q.2.1]? with
        | none => none
        | some r => applyRuleAt r sf q.2.2)
    (Primrec.snd.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
    hstep
  exact this.of_eq fun p => rfl

/-! ## A concrete word-indexed enumeration of context-sensitive languages

We make the enumeration concrete so that the *correctness* clause becomes definitional and the
remaining content splits cleanly into exactly two obligations: uniform computability of the
decider (`memOracle_computable`) and coverage of all CS languages (`enum_covers_CS`).

A context-sensitive (noncontracting) grammar is coded with nonterminals fixed to `ℕ`, as a
`Code T = List (grule T ℕ) × ℕ` (its rule list and initial symbol). `Code T` is `Primcodable`
via the existing `grulePrimcodable` instance, so it is decodable from a word.

Membership is decided by a **bounded search over derivation sequences**: a derivation sequence
`seq : List (ℕ × ℕ)` (rule index, position) is replayed from `[initial]` by `applyRuleSeq`, and
we check whether it yields exactly `v`. We search all sequences of length `≤ seqBound c v` whose
entries are bounded (rule index `< |rules|`, position `≤ |v| + 1`). This is a finite, computable
search (via the uniform `primrec_applyRuleSeq_uniform`), and for a noncontracting grammar the
bound is large enough to capture a witnessing derivation whenever `v` is in the language. -/

/-- A coded context-sensitive grammar: nonterminals are `ℕ`; the data is its rule list and
initial nonterminal. -/
abbrev Code (T : Type) := List (grule T ℕ) × ℕ

/-- Interpret a `Code` as an (unrestricted) grammar with `ℕ` nonterminals. -/
@[reducible] def ofCode (c : Code T) : grammar T := ⟨ℕ, c.2, c.1⟩

/-- Replay a derivation sequence from `[initial]` and check it yields exactly `v`. -/
def testData [DecidableEq T] (c : Code T) (seq : List (ℕ × ℕ)) (v : List T) : Bool :=
  decide (applyRuleSeq c.1 [symbol.nonterminal c.2] seq = some (v.map symbol.terminal))

/-- The finite alphabet of derivation steps `(rule index, position)` considered for `c`, `v`. -/
def seqAlphabet (c : Code T) (v : List T) : List (ℕ × ℕ) :=
  (List.range c.1.length).flatMap fun i =>
    (List.range (v.length + 2)).map fun p => (i, p)

/-- All lists of length exactly `k` over the alphabet `alph`. -/
def listsOfLen (alph : List (ℕ × ℕ)) : ℕ → List (List (ℕ × ℕ))
  | 0 => [[]]
  | (k + 1) => (listsOfLen alph k).flatMap fun l => alph.map fun a => a :: l

/-- Crude over-approximation of the length of a minimal witnessing derivation sequence (the
number of distinct bounded sentential forms). -/
def seqBound (c : Code T) (v : List T) : ℕ :=
  ((c.1.flatMap fun r =>
    r.input_L ++ symbol.nonterminal r.input_N :: r.input_R ++ r.output_string).length
    + v.length + 2) ^ (v.length + 2)

/-- All derivation sequences considered for `c`, `v` (length `≤ seqBound`, bounded entries). -/
def candidateSeqs (c : Code T) (v : List T) : List (List (ℕ × ℕ)) :=
  (List.range (seqBound c v + 1)).flatMap (listsOfLen (seqAlphabet c v))

/-- Bounded derivation-sequence search membership decider for a coded grammar. -/
def memCode [DecidableEq T] (c : Code T) (v : List T) : Bool :=
  (candidateSeqs c v).foldr (fun seq r => testData c seq v || r) false

/-- Decode a word into a coded grammar, indexing by the word's length (`List.length` is onto
`ℕ` for a nonempty alphabet, so this is surjective onto coded grammars). A default empty grammar
is used if the code is malformed. -/
noncomputable def decodeCode [Primcodable T] (u : List T) : Code T :=
  (Encodable.decode (α := Code T) u.length).getD ([], 0)

/-- The membership oracle: decode the index word into a coded grammar and run the bounded
search. -/
noncomputable def memOracle [DecidableEq T] [Primcodable T] (u v : List T) : Bool :=
  memCode (decodeCode u) v

/-- The enumerated language at index word `u`. Correctness against `memOracle` is definitional. -/
noncomputable def enumLang [DecidableEq T] [Primcodable T] (u : List T) : Language T :=
  {v | memOracle u v = true}

/-- `testData` is primrec jointly in the code, sequence, and word (uses the uniform
`applyRuleSeq` primrec). -/
private theorem testData_primrec [DecidableEq T] [Primcodable T] :
    Primrec (fun x : (Code T × List T) × List (ℕ × ℕ) => testData x.1.1 x.2 x.1.2) := by
  have hrules : Primrec (fun x : (Code T × List T) × List (ℕ × ℕ) => x.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hinit : Primrec (fun x : (Code T × List T) × List (ℕ × ℕ) =>
      [symbol.nonterminal (N := ℕ) x.1.1.2]) :=
    Primrec.list_cons.comp
      (primrec_symbol_nonterminal.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const ([] : List (symbol T ℕ)))
  have happ : Primrec (fun x : (Code T × List T) × List (ℕ × ℕ) =>
      applyRuleSeq x.1.1.1 [symbol.nonterminal x.1.1.2] x.2) :=
    primrec_applyRuleSeq_uniform.comp (Primrec.pair hrules (Primrec.pair hinit Primrec.snd))
  have htarget : Primrec (fun x : (Code T × List T) × List (ℕ × ℕ) =>
      (some (x.1.2.map symbol.terminal) : Option (List (symbol T ℕ)))) :=
    Primrec.option_some.comp
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (Primrec₂.mk (primrec_symbol_terminal.comp Primrec.snd)))
  exact (Primrec.eq (α := Option (List (symbol T ℕ)))).decide.comp happ htarget

/-- `listsOfLen` as an explicit `Nat.rec` (small-term form, proven by plain induction). -/
private theorem listsOfLen_eq (alph : List (ℕ × ℕ)) (n : ℕ) :
    listsOfLen alph n =
      Nat.rec (motive := fun _ => List (List (ℕ × ℕ))) [[]]
        (fun _ ih => ih.flatMap fun l => alph.map fun s => s :: l) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [listsOfLen, ih]

/-- `listsOfLen` (all lists of a given length over a given alphabet) is primrec jointly in the
alphabet and the length, via primitive recursion. -/
private theorem listsOfLen_primrec :
    Primrec (fun x : List (ℕ × ℕ) × ℕ => listsOfLen x.1 x.2) := by
  have hstep : Primrec₂ (fun (a : List (ℕ × ℕ) × ℕ) (q : ℕ × List (List (ℕ × ℕ))) =>
      q.2.flatMap fun l => a.1.map fun s => s :: l) := by
    apply Primrec₂.mk
    refine Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) ?_
    apply Primrec₂.mk
    exact Primrec.list_map (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec₂.mk (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine (Primrec.nat_rec' Primrec.snd (Primrec.const [[]]) hstep).of_eq fun x => ?_
  exact (listsOfLen_eq x.1 x.2).symm

/-- `seqAlphabet` is primrec. -/
private theorem seqAlphabet_primrec [DecidableEq T] [Primcodable T] :
    Primrec (fun p : Code T × List T => seqAlphabet p.1 p.2) := by
  have h : Primrec (fun p : Code T × List T =>
      (List.range p.1.1.length).flatMap fun i =>
        (List.range (p.2.length + 2)).map fun pos => (i, pos)) := by
    refine Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))) ?_
    apply Primrec₂.mk
    refine Primrec.list_map (Primrec.list_range.comp ?_) ?_
    · exact Primrec.nat_add.comp
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const 2)
    · exact Primrec₂.mk (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => rfl

/-- `seqBound` is primrec. -/
private theorem seqBound_primrec [DecidableEq T] [Primcodable T] :
    Primrec (fun p : Code T × List T => seqBound p.1 p.2) := by
  have hpow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hstepf : Primrec₂ (fun (_ : Code T × List T) (r : grule T ℕ) =>
      r.input_L ++ symbol.nonterminal r.input_N :: r.input_R ++ r.output_string) := by
    apply Primrec₂.mk
    exact Primrec.list_append.comp
      (Primrec.list_append.comp (primrec_grule_inputL.comp Primrec.snd)
        (Primrec.list_cons.comp
          (primrec_symbol_nonterminal.comp (primrec_grule_inputN.comp Primrec.snd))
          (primrec_grule_inputR.comp Primrec.snd)))
      (primrec_grule_outputString.comp Primrec.snd)
  have hlen : Primrec (fun p : Code T × List T =>
      (p.1.1.flatMap fun r =>
        r.input_L ++ symbol.nonterminal r.input_N :: r.input_R ++ r.output_string).length) :=
    Primrec.list_length.comp (Primrec.list_flatMap (Primrec.fst.comp Primrec.fst) hstepf)
  have hvlen : Primrec (fun p : Code T × List T => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hbase : Primrec (fun p : Code T × List T =>
      (p.1.1.flatMap fun r =>
        r.input_L ++ symbol.nonterminal r.input_N :: r.input_R ++ r.output_string).length
      + p.2.length + 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hlen hvlen) (Primrec.const 2)
  have hexp : Primrec (fun p : Code T × List T => p.2.length + 2) :=
    Primrec.nat_add.comp hvlen (Primrec.const 2)
  exact hpow.comp hbase hexp

/-- `candidateSeqs` is primrec. -/
private theorem candidateSeqs_primrec [DecidableEq T] [Primcodable T] :
    Primrec (fun p : Code T × List T => candidateSeqs p.1 p.2) := by
  have h : Primrec (fun p : Code T × List T =>
      (List.range (seqBound p.1 p.2 + 1)).flatMap (listsOfLen (seqAlphabet p.1 p.2))) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp seqBound_primrec)) ?_
    apply Primrec₂.mk
    exact listsOfLen_primrec.comp
      (Primrec.pair (seqAlphabet_primrec.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => rfl

/-- `memCode` is primrec jointly in the code and the word. -/
private theorem memCode_primrec [DecidableEq T] [Primcodable T] :
    Primrec (fun p : Code T × List T => memCode p.1 p.2) := by
  have hstep : Primrec₂ (fun (p : Code T × List T) (q : List (ℕ × ℕ) × Bool) =>
      testData p.1 q.1 p.2 || q.2) := by
    apply Primrec₂.mk
    have htd : Primrec (fun w : (Code T × List T) × (List (ℕ × ℕ) × Bool) =>
        testData w.1.1 w.2.1 w.1.2) :=
      testData_primrec.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    exact (Primrec.dom_bool₂ (· || ·)).comp htd (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr candidateSeqs_primrec (Primrec.const false) hstep

/-- **Obligation 1 (uniform computability), now discharged.** The bounded derivation-sequence
search oracle is computable jointly in the grammar-code word and the input word: `decodeCode` is
`Encodable.decode ∘ encode` and `memCode` is the bounded search, primrec via the uniform
`primrec_applyRuleSeq_uniform`. -/
public theorem memOracle_computable [DecidableEq T] [Fintype T] [Primcodable T] :
    Computable (fun p : List T × List T => memOracle p.1 p.2) := by
  have hdec : Primrec (fun u : List T => decodeCode u) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.list_length) (Primrec.const ([], 0))
  exact (memCode_primrec.comp (Primrec.pair (hdec.comp Primrec.fst) Primrec.snd)).to_comp

/-! ### Coverage: every CS language is enumerated

The proof has two easy structural ingredients (here) and one hard combinatorial ingredient
(the bounded-witness lemma `memCode_complete`). -/

/-- `foldr`-`or` over the candidate sequences is the existential "some sequence witnesses". -/
private theorem foldr_or_eq_true {α : Type} (p : α → Bool) (l : List α) :
    l.foldr (fun a r => p a || r) false = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.foldr_cons, Bool.or_eq_true, ih]; simp [List.mem_cons, or_and_right,
      exists_or]

/-- **Coverage, soundness side.** If the bounded search accepts, the word is in the language. -/
private theorem memCode_sound [DecidableEq T] (c : Code T) (v : List T)
    (h : memCode c v = true) : v ∈ grammar_language (ofCode c) := by
  rw [memCode, foldr_or_eq_true] at h
  obtain ⟨seq, _, htest⟩ := h
  rw [testData, decide_eq_true_eq] at htest
  exact applyRuleSeq_derives (ofCode c) [symbol.nonterminal c.2]
    (v.map symbol.terminal) seq htest

/-- A `none`-absorbing `Option`-valued `foldl` factors through `Option.bind`. -/
private theorem foldl_option_bind {α β : Type} (step : Option α → β → Option α)
    (hstep : ∀ x, step none x = none) :
    ∀ (t : List β) (b : Option α),
      List.foldl step b t = b.bind (fun m => List.foldl step (some m) t) := by
  intro t
  induction t with
  | nil => intro b; cases b <;> rfl
  | cons a t ih =>
    intro b
    cases b with
    | none => rw [List.foldl_cons, hstep a]; exact ih none
    | some m => rfl

/-- `applyRuleSeq` splits over concatenation of derivation sequences. -/
private theorem applyRuleSeq_append {N : Type} [DecidableEq T] [DecidableEq N]
    (rules : List (grule T N)) (init : List (symbol T N)) (s t : List (ℕ × ℕ)) :
    applyRuleSeq rules init (s ++ t)
      = (applyRuleSeq rules init s).bind (fun m => applyRuleSeq rules m t) := by
  simp only [applyRuleSeq, List.foldl_append]
  exact foldl_option_bind _ (fun _ => rfl) t (List.foldl _ (some init) s)

/-- Membership in `listsOfLen`: exactly the lists of the given length over the alphabet. -/
private theorem mem_listsOfLen (alph : List (ℕ × ℕ)) (k : ℕ) (l : List (ℕ × ℕ)) :
    l ∈ listsOfLen alph k ↔ l.length = k ∧ ∀ e ∈ l, e ∈ alph := by
  induction k generalizing l with
  | zero =>
    simp only [listsOfLen, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, by simp⟩
    · rintro ⟨hlen, -⟩; exact List.length_eq_zero_iff.mp hlen
  | succ k ih =>
    simp only [listsOfLen, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨l', hl', a, ha, rfl⟩
      obtain ⟨hlen, hmem⟩ := ih l' |>.mp hl'
      refine ⟨by simp [hlen], ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ha
      · exact hmem e he'
    · rintro ⟨hlen, hmem⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        refine ⟨l', (ih l').mpr ⟨by simpa using hlen, fun e he => hmem e (by simp [he])⟩,
          a, hmem a (by simp), rfl⟩

/-- A successful non-contracting rule application does not shorten the sentential form. -/
private theorem applyRuleAt_length_le {N : Type} [DecidableEq T] [DecidableEq N]
    {r : grule T N} (hr : grule_noncontracting r) {sf sf' : List (symbol T N)} {p : ℕ}
    (happ : applyRuleAt r sf p = some sf') : sf.length ≤ sf'.length := by
  obtain ⟨u, w, hbef, haft⟩ := applyRuleAt_correct r sf sf' p happ
  rw [hbef, haft]
  simp only [List.length_append, List.length_cons, List.length_nil,
    grule_noncontracting] at hr ⊢
  omega

/-- Every symbol of a form reachable by `applyRuleSeq` lies in the initial form or some rule
output. -/
private theorem applyRuleSeq_symbols {N : Type} [DecidableEq T] [DecidableEq N]
    (rules : List (grule T N)) (A : symbol T N → Prop)
    (hrules : ∀ r ∈ rules, ∀ x ∈ r.output_string, A x) :
    ∀ (seq : List (ℕ × ℕ)) (init sf : List (symbol T N)),
      applyRuleSeq rules init seq = some sf → (∀ x ∈ init, A x) → ∀ x ∈ sf, A x := by
  intro seq
  induction seq with
  | nil => intro init sf happ hinit; cases happ; exact hinit
  | cons a seq ih =>
    intro init sf happ hinit
    rw [show a :: seq = [a] ++ seq from rfl, applyRuleSeq_append] at happ
    rcases hm : applyRuleSeq rules init [a] with _ | mid
    · rw [hm] at happ; simp at happ
    · rw [hm] at happ
      refine ih mid sf happ ?_
      -- mid's symbols are in A
      simp only [applyRuleSeq, List.foldl_cons, List.foldl_nil] at hm
      rcases hr : rules[a.1]? with _ | r
      · rw [hr] at hm; simp at hm
      · rw [hr] at hm
        obtain ⟨u, w, hbef, haft⟩ := applyRuleAt_correct r init mid a.2 hm
        intro x hx
        rw [haft] at hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hinit x (by rw [hbef]; simp [hx])
        · exact hrules r (List.mem_of_getElem? hr) x hx
        · exact hinit x (by rw [hbef]; simp [hx])

/-- A successful application's position is within the sentential form. -/
private theorem applyRuleAt_pos_le {N : Type} [DecidableEq T] [DecidableEq N]
    {r : grule T N} {sf sf' : List (symbol T N)} {p : ℕ}
    (h : applyRuleAt r sf p = some sf') : p ≤ sf.length := by
  by_contra hp
  push_neg at hp
  unfold applyRuleAt at h
  rw [List.drop_eq_nil_of_le (le_of_lt hp)] at h
  simp at h

/-- `applyRuleSeq` is length non-decreasing for noncontracting grammars. -/
private theorem applyRuleSeq_length_le {N : Type} [DecidableEq T] [DecidableEq N]
    (rules : List (grule T N)) (hnc : ∀ r ∈ rules, grule_noncontracting r) :
    ∀ (seq : List (ℕ × ℕ)) (init sf : List (symbol T N)),
      applyRuleSeq rules init seq = some sf → init.length ≤ sf.length := by
  intro seq
  induction seq with
  | nil => intro init sf h; cases h; exact le_refl _
  | cons a seq ih =>
    intro init sf h
    rw [show a :: seq = [a] ++ seq from rfl, applyRuleSeq_append] at h
    rcases hm : applyRuleSeq rules init [a] with _ | mid
    · rw [hm] at h; simp at h
    · rw [hm] at h
      refine le_trans ?_ (ih mid sf h)
      simp only [applyRuleSeq, List.foldl_cons, List.foldl_nil] at hm
      rcases hr : rules[a.1]? with _ | r
      · rw [hr] at hm; simp at hm
      · rw [hr] at hm; exact applyRuleAt_length_le (hnc r (List.mem_of_getElem? hr)) hm

/-- A duplicate-free list of sentential forms of length `≤ n` over a finite symbol alphabet `A`
has at most `(|A| + 1) ^ (n + 1)` elements. -/
private theorem nodup_forms_card_bound [DecidableEq T] (A : Finset (symbol T ℕ)) (n : ℕ)
    (l : List (List (symbol T ℕ))) (hnd : l.Nodup)
    (hlen : ∀ f ∈ l, f.length ≤ n) (hsym : ∀ f ∈ l, ∀ x ∈ f, x ∈ A) :
    l.length ≤ (A.card + 1) ^ (n + 1) := by
  classical
  set enc : List (symbol T ℕ) → (Fin (n + 1) → Option {x // x ∈ A}) :=
    fun f i => (f[i.val]?).bind (fun x => if hx : x ∈ A then some ⟨x, hx⟩ else none) with henc
  have hmapval : ∀ f ∈ l, ∀ i : Fin (n + 1), (enc f i).map Subtype.val = f[i.val]? := by
    intro f hf i
    rcases hfi : f[i.val]? with _ | x
    · simp [henc, hfi]
    · have hx : x ∈ A := hsym f hf x (List.mem_of_getElem? hfi)
      simp [henc, hfi, hx]
  have hinj : Set.InjOn enc {f | f ∈ l} := by
    intro f hf g hg hfg
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n + 1
    · have h1 := hmapval f hf ⟨i, hi⟩
      have h2 := hmapval g hg ⟨i, hi⟩
      rw [← h1, ← h2, congrFun hfg ⟨i, hi⟩]
    · rw [List.getElem?_eq_none (by have := hlen f hf; omega),
        List.getElem?_eq_none (by have := hlen g hg; omega)]
  have hmapnd : (l.map enc).Nodup := hnd.map_on hinj
  have hcard := hmapnd.length_le_card
  rwa [List.length_map, Fintype.card_fun, Fintype.card_option, Fintype.card_coe,
    Fintype.card_fin] at hcard

/-- For a context-sensitive coded grammar, applying a sequence to a start symbol-free form is
length non-decreasing (the only contracting rule `S → ε` cannot fire without `S`). -/
private theorem applyRuleSeq_length_le_noS [DecidableEq T] (c : Code T)
    (hcs1 : ∀ r ∈ c.1, initial_epsilon_rule (ofCode c) r ∨ grule_noncontracting r)
    (hnir : initial_not_on_rhs (ofCode c)) :
    ∀ (seq : List (ℕ × ℕ)) (F sf : List (symbol T ℕ)),
      applyRuleSeq c.1 F seq = some sf → symbol.nonterminal c.2 ∉ F → F.length ≤ sf.length := by
  intro seq
  induction seq with
  | nil => intro F sf h _; cases h; exact le_refl _
  | cons a seq ih =>
    intro F sf h hF
    rw [show a :: seq = [a] ++ seq from rfl, applyRuleSeq_append] at h
    rcases hm : applyRuleSeq c.1 F [a] with _ | mid
    · rw [hm] at h; simp at h
    · rw [hm] at h
      simp only [applyRuleSeq, List.foldl_cons, List.foldl_nil] at hm
      rcases hr : c.1[a.1]? with _ | r
      · rw [hr] at hm; simp at hm
      · rw [hr] at hm
        obtain ⟨u, w, hbef, haft⟩ := applyRuleAt_correct r F mid a.2 hm
        have hrnc : grule_noncontracting r := by
          rcases hcs1 r (List.mem_of_getElem? hr) with he | hnc
          · exfalso; apply hF; rw [hbef, he.2.1]; simp
          · exact hnc
        have hmidnoS : symbol.nonterminal c.2 ∉ mid := by
          rw [haft]
          simp only [List.mem_append, not_or]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro hc; exact hF (by rw [hbef]; simp [hc])
          · exact hnir r (List.mem_of_getElem? hr)
          · intro hc; exact hF (by rw [hbef]; simp [hc])
        exact le_trans (applyRuleAt_length_le hrnc hm) (ih mid sf h hmidnoS)

/-- Any form reached by at least one derivation step (from the start symbol) no longer contains
the start symbol (it does not occur on any rule's right-hand side). -/
private theorem reachable_noS [DecidableEq T] (c : Code T)
    (hnir : initial_not_on_rhs (ofCode c)) (a : ℕ × ℕ) (seq : List (ℕ × ℕ))
    (sf : List (symbol T ℕ))
    (h : applyRuleSeq c.1 [symbol.nonterminal c.2] (a :: seq) = some sf) :
    symbol.nonterminal c.2 ∉ sf := by
  rw [show a :: seq = [a] ++ seq from rfl, applyRuleSeq_append] at h
  rcases hm : applyRuleSeq c.1 [symbol.nonterminal c.2] [a] with _ | mid
  · rw [hm] at h; simp at h
  · rw [hm] at h
    have hmidnoS : symbol.nonterminal c.2 ∉ mid := by
      simp only [applyRuleSeq, List.foldl_cons, List.foldl_nil] at hm
      rcases hr : c.1[a.1]? with _ | r
      · rw [hr] at hm; simp at hm
      · rw [hr] at hm
        obtain ⟨u, w, hbef, haft⟩ :=
          applyRuleAt_correct r [symbol.nonterminal c.2] mid a.2 hm
        have hulen : u = [] ∧ r.input_R = [] ∧ w = [] := by
          have hl := congrArg List.length hbef
          simp only [List.length_append, List.length_cons, List.length_singleton,
            List.length_nil] at hl
          refine ⟨?_, ?_, ?_⟩ <;> (apply List.eq_nil_of_length_eq_zero; omega)
        rw [haft, hulen.1, hulen.2.2]
        simpa using hnir r (List.mem_of_getElem? hr)
    intro hx
    exact applyRuleSeq_symbols c.1 (fun y => y ≠ symbol.nonterminal c.2)
      (fun r hr y hy hc => hnir r hr (hc ▸ hy)) seq mid sf h
      (fun y hy hc => hmidnoS (hc ▸ hy)) (symbol.nonterminal c.2) hx rfl

/-- The witnessing-sequence form of language membership. -/
private theorem exists_applyRuleSeq_of_mem [DecidableEq T] (c : Code T) (v : List T)
    (h : v ∈ grammar_language (ofCode c)) :
    ∃ seq : List (ℕ × ℕ),
      applyRuleSeq c.1 [symbol.nonterminal c.2] seq = some (v.map symbol.terminal) := by
  obtain ⟨seq, hseq⟩ := grammarTest_complete (ofCode c) v h
  refine ⟨seq, ?_⟩
  unfold grammarTest at hseq
  rcases hr : applyRuleSeq (ofCode c).rules [symbol.nonterminal (ofCode c).initial] seq with _ | sf
  · rw [hr] at hseq; simp at hseq
  · rw [hr, beq_iff_eq, extractTerminals_eq_map_iff] at hseq
    rw [hseq]

/-- **Coverage, completeness side (the hard bounded-witness lemma).** For a context-sensitive
coded grammar, if `v` is in the language then there is a witnessing derivation sequence within
the search bound. -/
private theorem memCode_complete [DecidableEq T] (c : Code T) (v : List T)
    (hcs : grammar_context_sensitive (ofCode c))
    (h : v ∈ grammar_language (ofCode c)) : memCode c v = true := by
  classical
  rw [memCode, foldr_or_eq_true]
  -- the alphabet of symbols occurring in the grammar
  set ruleSyms : List (symbol T ℕ) :=
    c.1.flatMap fun r =>
      r.input_L ++ symbol.nonterminal r.input_N :: r.input_R ++ r.output_string with hruleSyms
  set A : Finset (symbol T ℕ) := (symbol.nonterminal c.2 :: ruleSyms).toFinset with hA
  -- a witnessing sequence exists; take a minimal-length one
  have hPex : ∃ n, ∃ seq : List (ℕ × ℕ), seq.length = n ∧
      applyRuleSeq c.1 [symbol.nonterminal c.2] seq = some (v.map symbol.terminal) := by
    obtain ⟨seq, hseq⟩ := exists_applyRuleSeq_of_mem c v h
    exact ⟨seq.length, seq, rfl, hseq⟩
  obtain ⟨seq, hseqlen, hseqapp⟩ := Nat.find_spec hPex
  set m := Nat.find hPex with hm
  have hmin : ∀ k < m, ¬ ∃ s : List (ℕ × ℕ), s.length = k ∧
      applyRuleSeq c.1 [symbol.nonterminal c.2] s = some (v.map symbol.terminal) :=
    fun k hk => Nat.find_min hPex hk
  -- prefix forms
  set pform : ℕ → List (symbol T ℕ) :=
    fun i => (applyRuleSeq c.1 [symbol.nonterminal c.2] (seq.take i)).getD [] with hpform
  -- each prefix result is `some`
  have hsome : ∀ i ≤ seq.length,
      applyRuleSeq c.1 [symbol.nonterminal c.2] (seq.take i) = some (pform i) := by
    intro i hi
    have hsplit : seq = seq.take i ++ seq.drop i := by rw [List.take_append_drop]
    rw [hsplit, applyRuleSeq_append] at hseqapp
    rcases hpi : applyRuleSeq c.1 [symbol.nonterminal c.2] (seq.take i) with _ | F
    · rw [hpi] at hseqapp; simp at hseqapp
    · simp only [hpform, hpi, Option.getD_some]
  -- the suffix from each prefix form still reaches the target
  have hsuffix : ∀ i ≤ seq.length,
      applyRuleSeq c.1 (pform i) (seq.drop i) = some (v.map symbol.terminal) := by
    intro i hi
    have hsplit : seq = seq.take i ++ seq.drop i := (List.take_append_drop i seq).symm
    have := hseqapp
    rw [hsplit, applyRuleSeq_append, hsome i hi] at this
    simpa using this
  -- prefix forms have length ≤ |v| + 1 and symbols in A
  have hsymrules : ∀ r ∈ c.1, ∀ x ∈ r.output_string, x ∈ (symbol.nonterminal c.2 :: ruleSyms) := by
    intro r hr x hx
    refine List.mem_cons_of_mem _ ?_
    rw [hruleSyms, List.mem_flatMap]
    exact ⟨r, hr, by simp [hx]⟩
  have hformsym : ∀ i ≤ seq.length, ∀ x ∈ pform i, x ∈ A := by
    intro i hi x hx
    rw [hA, List.mem_toFinset]
    refine applyRuleSeq_symbols c.1 (fun y => y ∈ symbol.nonterminal c.2 :: ruleSyms)
      hsymrules (seq.take i) [symbol.nonterminal c.2] (pform i) (hsome i hi) ?_ x hx
    intro y hy; rw [List.mem_singleton] at hy; subst hy; exact List.mem_cons_self ..
  -- length bound (handling the optional `S → ε` rule via noncontracting case split)
  have hformlen : ∀ i ≤ seq.length, (pform i).length ≤ v.length + 1 := by
    intro i hi
    by_cases hnc : ∀ r ∈ c.1, grule_noncontracting r
    · have hle := applyRuleSeq_length_le c.1 hnc (seq.drop i) (pform i)
        (v.map symbol.terminal) (hsuffix i hi)
      simp only [List.length_map] at hle; omega
    · have hnir : initial_not_on_rhs (ofCode c) := by
        apply hcs.2
        push_neg at hnc
        obtain ⟨r, hr, hrnc⟩ := hnc
        rcases hcs.1 r hr with he | hc
        · exact ⟨r, hr, he⟩
        · exact absurd hc hrnc
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have h0 : pform 0 = [symbol.nonterminal c.2] := by
          rw [hpform]; simp [applyRuleSeq]
        rw [h0]; simp
      · have hnoS : symbol.nonterminal c.2 ∉ pform i := by
          have hsi := hsome i hi
          rcases htk : seq.take i with _ | ⟨a, rest⟩
          · exfalso
            have : (seq.take i).length = 0 := by rw [htk]; rfl
            rw [List.length_take, Nat.min_eq_left hi] at this; omega
          · rw [htk] at hsi
            exact reachable_noS c hnir a rest (pform i) hsi
        have hle := applyRuleSeq_length_le_noS c hcs.1 hnir (seq.drop i) (pform i)
          (v.map symbol.terminal) (hsuffix i hi) hnoS
        simp only [List.length_map] at hle; omega
  -- prefix forms are pairwise distinct (else a shorter witness exists, contradicting minimality)
  have hdistinct : ∀ i j, i ≤ seq.length → j ≤ seq.length → i < j → pform i ≠ pform j := by
    intro i j hi hj hij hpij
    have hsplice : applyRuleSeq c.1 [symbol.nonterminal c.2] (seq.take i ++ seq.drop j)
        = some (v.map symbol.terminal) := by
      rw [applyRuleSeq_append, hsome i hi, hpij]
      exact hsuffix j hj
    have hlen' : (seq.take i ++ seq.drop j).length < m := by
      rw [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left hi, ← hseqlen]
      omega
    exact hmin _ hlen' ⟨_, rfl, hsplice⟩
  -- count: the `m + 1` distinct prefix forms fit in the bound
  have hpfsnd : ((List.range (m + 1)).map pform).Nodup := by
    apply (List.nodup_range).map_on
    intro i hi j hj hpij
    rw [List.mem_range] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact hdistinct i j (by omega) (by omega) h hpij
    · exact hdistinct j i (by omega) (by omega) (by omega) hpij.symm
  have hcount : m + 1 ≤ (A.card + 1) ^ (v.length + 1 + 1) := by
    have := nodup_forms_card_bound A (v.length + 1) ((List.range (m + 1)).map pform) hpfsnd
      (by intro f hf; rw [List.mem_map] at hf; obtain ⟨i, hi, rfl⟩ := hf
          exact hformlen i (by rw [List.mem_range] at hi; omega))
      (by intro f hf; rw [List.mem_map] at hf; obtain ⟨i, hi, rfl⟩ := hf
          exact hformsym i (by rw [List.mem_range] at hi; omega))
    rwa [List.length_map, List.length_range] at this
  have hm_le : m ≤ seqBound c v := by
    have hAcard : A.card + 1 ≤ ruleSyms.length + v.length + 2 := by
      have : A.card ≤ (symbol.nonterminal c.2 :: ruleSyms).length :=
        le_trans (List.toFinset_card_le _) (le_refl _)
      simp only [List.length_cons] at this; omega
    have hpow : (A.card + 1) ^ (v.length + 1 + 1) ≤ seqBound c v := by
      rw [seqBound, ← hruleSyms]
      exact Nat.pow_le_pow_left (by omega) _
    omega
  -- every step index/position lies in the alphabet `seqAlphabet`
  have hentries : ∀ e ∈ seq, e ∈ seqAlphabet c v := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hstep : applyRuleSeq c.1 (pform k) [seq[k]] = some (pform (k + 1)) := by
      have h1 := hsome (k + 1) (by omega)
      rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some,
        applyRuleSeq_append, hsome k (by omega)] at h1
      simpa using h1
    simp only [applyRuleSeq, List.foldl_cons, List.foldl_nil] at hstep
    rcases hr : c.1[seq[k].1]? with _ | r
    · rw [hr] at hstep; simp at hstep
    · rw [hr] at hstep
      rw [seqAlphabet, List.mem_flatMap]
      refine ⟨seq[k].1, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hr).1, ?_⟩
      rw [List.mem_map]
      refine ⟨seq[k].2, List.mem_range.mpr ?_, rfl⟩
      have := applyRuleAt_pos_le hstep
      have := hformlen k (by omega)
      omega
  refine ⟨seq, ?_, ?_⟩
  · rw [candidateSeqs, List.mem_flatMap]
    refine ⟨m, List.mem_range.mpr (by omega), ?_⟩
    rw [mem_listsOfLen]
    exact ⟨hseqlen, hentries⟩
  · rw [testData, decide_eq_true_eq]; exact hseqapp

/-- Restricting a context-sensitive grammar to its used nonterminals stays context-sensitive. -/
private theorem restrictGrammar_context_sensitive (g : grammar T)
    (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (restrictGrammar g) := by
  classical
  obtain ⟨hrules, heps⟩ := hg
  refine ⟨?_, ?_⟩
  · intro r' hr'
    obtain ⟨r, hr, hL, hN, hR, hout⟩ := restrictGrammar_rule_mem hr'
    rcases hrules r hr with he | hnc
    · left
      obtain ⟨heL, heN, heR, heout⟩ := he
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hL, heL]; rfl
      · rw [hN, heN]; exact restrictNT_of_mem (initial_mem_usedNTs g)
      · rw [hR, heR]; rfl
      · rw [hout, heout]; rfl
    · right
      simp only [grule_noncontracting, hL, hR, hout, List.length_map]
      simpa [grule_noncontracting] using hnc
  · rintro ⟨r', hr', he'⟩
    obtain ⟨r, hr, hL, hN, hR, hout⟩ := restrictGrammar_rule_mem hr'
    obtain ⟨heL, heN, heR, heout⟩ := he'
    have hrn : r.input_N = g.initial := by
      have hh : restrictNT g r.input_N = (restrictGrammar g).initial := hN ▸ heN
      rw [restrictNT_of_mem (ruleNT_mem_usedNTs hr (inputN_mem_ruleNTs r))] at hh
      exact Subtype.mk.inj hh
    have hr_eps : initial_epsilon_rule g r :=
      ⟨List.map_eq_nil_iff.mp (hL ▸ heL), hrn,
        List.map_eq_nil_iff.mp (hR ▸ heR), List.map_eq_nil_iff.mp (hout ▸ heout)⟩
    have hnir := heps ⟨r, hr, hr_eps⟩
    intro r'' hr''
    obtain ⟨rr, hrr, hL2, hN2, hR2, hout2⟩ := restrictGrammar_rule_mem hr''
    rw [hout2]
    intro hmem
    obtain ⟨s, hs, hseq⟩ := List.mem_map.1 hmem
    cases s with
    | terminal t => simp [restrictSym] at hseq
    | nonterminal n =>
      simp only [restrictSym] at hseq
      have hnu : n ∈ usedNTs g :=
        ruleNT_mem_usedNTs hrr (by
          rw [ruleNTs, List.mem_append]; right; exact mem_symbolsNTs_iff.mpr hs)
      have hni : restrictNT g n = (restrictGrammar g).initial := symbol.nonterminal.inj hseq
      rw [restrictNT_of_mem hnu] at hni
      have : n = g.initial := Subtype.mk.inj hni
      subst this
      exact hnir rr hrr hs

/-- Relabel a finite-nonterminal grammar to one with `ℕ` nonterminals (a `Code`), preserving
the language and context-sensitivity. Uses the `lifted_grammar_` relabeling machinery with the
injection `g₀.nt ↪ ℕ` coming from `Fintype.equivFin`. -/
private theorem code_of_finite [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt]
    [DecidableEq g₀.nt] (hcs : grammar_context_sensitive g₀) :
    ∃ c : Code T, grammar_context_sensitive (ofCode c)
      ∧ grammar_language (ofCode c) = grammar_language g₀ := by
  classical
  set ι : g₀.nt → ℕ := fun x => (Fintype.equivFin g₀.nt x : Fin _).1 with hι
  have ιinj : Function.Injective ι := fun a b hab =>
    (Fintype.equivFin g₀.nt).injective (Fin.val_injective hab)
  set σ : ℕ → Option g₀.nt := fun n =>
    if h : n < Fintype.card g₀.nt then some ((Fintype.equivFin g₀.nt).symm ⟨n, h⟩) else none
    with hσ
  set c : Code T := (g₀.rules.map (lift_rule_ ι), ι g₀.initial) with hc
  have hofc : ofCode c = ⟨ℕ, ι g₀.initial, g₀.rules.map (lift_rule_ ι)⟩ := rfl
  have hσι : ∀ n₀ : g₀.nt, σ (ι n₀) = some n₀ := by
    intro n₀
    have hlt : ι n₀ < Fintype.card g₀.nt := (Fintype.equivFin g₀.nt n₀).2
    have hfin : (⟨ι n₀, hlt⟩ : Fin (Fintype.card g₀.nt)) = Fintype.equivFin g₀.nt n₀ :=
      Fin.ext rfl
    simp only [hσ, dif_pos hlt, hfin, Equiv.symm_apply_apply]
  -- the relabeled grammar, packaged as a `lifted_grammar_`
  let lg : lifted_grammar_ T :=
    { g₀ := g₀, g := ofCode c, lift_nt := ι, sink_nt := σ, lift_inj := ιinj
      sink_inj := by
        intro x y hxy
        by_cases hx : x < Fintype.card g₀.nt
        · by_cases hy : y < Fintype.card g₀.nt
          · left
            simp only [hσ, dif_pos hx, dif_pos hy] at hxy
            have := (Fintype.equivFin g₀.nt).symm.injective (Option.some.inj hxy)
            exact congrArg Fin.val this
          · simp only [hσ, dif_pos hx, dif_neg hy] at hxy
            exact absurd hxy (Option.some_ne_none _)
        · right; simp only [hσ, dif_neg hx]
      lift_nt_sink := hσι
      corresponding_rules := fun r hr => by
        show lift_rule_ ι r ∈ g₀.rules.map (lift_rule_ ι)
        exact List.mem_map_of_mem hr
      preimage_of_rules := by
        rintro r ⟨hr, -⟩
        rcases List.mem_map.1 hr with ⟨r₀, hr₀, rfl⟩
        exact ⟨r₀, hr₀, rfl⟩ }
  have hlang : grammar_language (ofCode c) = grammar_language g₀ := by
    apply Set.eq_of_subset_of_subset
    · -- ofCode c ⊆ g₀ via sink
      intro w hw
      have hgood : good_string_ (lg := lg) [symbol.nonterminal (ι g₀.initial)] := by
        intro a ha
        rw [List.mem_singleton] at ha; subst ha
        exact ⟨g₀.initial, hσι g₀.initial⟩
      have := sink_deri_ lg (w₁ := [symbol.nonterminal (ι g₀.initial)])
        (w₂ := w.map symbol.terminal) hw hgood
      rw [sink_string_map_terminal_ σ w] at this
      have hs : sink_string_ σ ([symbol.nonterminal (ι g₀.initial)] : List (symbol T ℕ))
          = [symbol.nonterminal g₀.initial] := by
        simp [sink_string_, sink_symbol_, hσι]
      rw [hs] at this
      exact this
    · -- g₀ ⊆ ofCode c via lift
      intro w hw
      have := lift_deri_ lg (w₁ := [symbol.nonterminal g₀.initial])
        (w₂ := w.map symbol.terminal) hw
      rw [lift_string_map_terminal_ ι w] at this
      have hs : lift_string_ ι ([symbol.nonterminal g₀.initial] : List (symbol T g₀.nt))
          = [symbol.nonterminal (ι g₀.initial)] := rfl
      rw [hs] at this
      exact this
  refine ⟨c, ?_, hlang⟩
  -- context-sensitivity is preserved (lengths and the ε/initial structure are preserved)
  obtain ⟨hrules, heps⟩ := hcs
  constructor
  · intro r' hr'
    rcases List.mem_map.1 hr' with ⟨r, hr, rfl⟩
    rcases hrules r hr with he | hnc
    · left
      obtain ⟨heL, heN, heR, heout⟩ := he
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [lift_rule_, lift_string_, heL]
      · show ι r.input_N = (ofCode c).initial
        rw [heN]
      · simp [lift_rule_, lift_string_, heR]
      · simp [lift_rule_, lift_string_, heout]
    · right
      simp only [grule_noncontracting, lift_rule_, lift_string_, List.length_map]
      exact hnc
  · rintro ⟨r', hr', he'⟩
    rcases List.mem_map.1 hr' with ⟨r, hr, rfl⟩
    have hr_eps : initial_epsilon_rule g₀ r := by
      obtain ⟨heL, heN, heR, heout⟩ := he'
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [lift_rule_, lift_string_] using heL
      · exact ιinj (by simpa [lift_rule_] using heN)
      · simpa [lift_rule_, lift_string_] using heR
      · simpa [lift_rule_, lift_string_] using heout
    have hnir := heps ⟨r, hr, hr_eps⟩
    intro r'' hr''
    rcases List.mem_map.1 hr'' with ⟨rr, hrr, rfl⟩
    simp only [lift_rule_, lift_string_, List.mem_map, not_exists, not_and]
    rintro s hs hseq
    cases s with
    | terminal t => simp [lift_symbol_] at hseq
    | nonterminal n =>
      have hn : ι n = (ofCode c).initial := by simpa [lift_symbol_] using hseq
      have : n = g₀.initial := ιinj (show ι n = ι g₀.initial from hn)
      subst this
      exact hnir rr hrr hs

/-- **Encoding.** Every context-sensitive language is the language of a context-sensitive coded
grammar (nonterminals renamed to `ℕ`). -/
private theorem code_of_CS [DecidableEq T] {L : Language T} (hL : is_CS L) :
    ∃ c : Code T, grammar_context_sensitive (ofCode c) ∧ grammar_language (ofCode c) = L := by
  classical
  obtain ⟨g, hcs, hlang⟩ := hL
  obtain ⟨c, hc_cs, hc_lang⟩ := code_of_finite (restrictGrammar g)
    (restrictGrammar_context_sensitive g hcs)
  exact ⟨c, hc_cs, by rw [hc_lang, ← grammar_language_eq_restrictGrammar, hlang]⟩

/-- **Surjectivity of decoding.** Every coded grammar is `decodeCode u` for some index word
`u` — because `List T` is denumerable for a nonempty alphabet, so `Encodable.encode` is onto. -/
private theorem decodeCode_surj [Primcodable T] [Nonempty T] (c : Code T) :
    ∃ u : List T, decodeCode u = c := by
  refine ⟨List.replicate (Encodable.encode c) (Classical.arbitrary T), ?_⟩
  rw [decodeCode, List.length_replicate, Encodable.encodek, Option.getD_some]

/-- **Obligation 2 (coverage).** Every context-sensitive language is `enumLang u` for some index
word `u`. Assembled from `memCode_sound`/`memCode_complete` (membership correctness),
`code_of_CS` (encoding), and `decodeCode_surj` (surjectivity). -/
public theorem enum_covers_CS [DecidableEq T] [Fintype T] [Primcodable T] [Nonempty T] :
    ∀ L : Language T, is_CS L → ∃ u, enumLang u = L := by
  intro L hL
  obtain ⟨c, hcs, hlang⟩ := code_of_CS hL
  subst hlang
  obtain ⟨u, hu⟩ := decodeCode_surj c
  refine ⟨u, ?_⟩
  have h1 : enumLang u = {v | memCode c v = true} := by
    rw [enumLang]; ext w; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, memOracle, hu]
  rw [h1]
  ext v
  exact ⟨fun hm => memCode_sound c v hm, fun hv => memCode_complete c v hcs hv⟩

/-- **Effective enumeration of context-sensitive languages**, assembled from the two obligations
`memOracle_computable` and `enum_covers_CS` (the correctness clause is definitional, since
`enumLang u` is *defined* as `{v | memOracle u v = true}`). -/
public theorem exists_cs_enumeration
    [DecidableEq T] [Fintype T] [Primcodable T] [Nonempty T] :
    ∃ (e : List T → Language T) (mem : List T → List T → Bool),
      (∀ u v, mem u v = true ↔ v ∈ e u) ∧
      Computable (fun p : List T × List T => mem p.1 p.2) ∧
      (∀ L : Language T, is_CS L → ∃ u, e u = L) :=
  ⟨enumLang, memOracle, fun _ _ => Iff.rfl, memOracle_computable, enum_covers_CS⟩

/-- **Context-sensitive languages are a strict subclass of the recursive languages**,
`CS ⊊ Recursive`. Assembled from the proven diagonalization core `diagonal_strict` and the
enumeration obligation `exists_cs_enumeration`. (Nonemptiness of the alphabet is necessary:
over an empty alphabet `CS = Recursive`.) -/
public theorem CS_strict_subclass_Recursive
    [DecidableEq T] [Fintype T] [Primcodable T] [Nonempty T] :
    (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) := by
  obtain ⟨e, mem, hmem, hmem_comp, hsurj⟩ := exists_cs_enumeration (T := T)
  exact diagonal_strict e mem hmem hmem_comp hsurj
