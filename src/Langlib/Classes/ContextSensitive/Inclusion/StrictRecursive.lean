module

public import Langlib.Classes.ContextSensitive.Decidability.Membership
public import Langlib.Classes.ContextSensitive.Inclusion.Recursive
@[expose]
public section



/-! # Strict Inclusion: CS ⊊ Recursive

Context-sensitive languages form a *strict* subclass of the recursive languages.

The proof is based on **diagonalization**.

The uniform computable membership oracle for context-sensitive grammars
(`memCode` / `contextSensitive_computableMembership`, in
`Classes/ContextSensitive/Decidability/Membership.lean`) supplies a surjective enumeration
`e : List T → Language T` of all context-sensitive languages and a total computable
`mem : List T → List T → Bool` with `mem u v = true ↔ v ∈ e u`. Define `D = {v | v ∉ e v}`. Then
`D` is recursive, since its characteristic predicate `v ↦ mem v v` is computable. And `D` is not
context-sensitive: if `e u = D` for some `u`, instantiating the definition of `D` at `v = u` and
substituting `e u = D` gives `u ∈ D ↔ u ∉ e u ↔ u ∉ D`, a contradiction; hence `D` is not in the
range of `e`. Therefore `D` is recursive but not context-sensitive, so `CS ⊊ Recursive`.

The argument requires `mem` to be total and computable, which holds for CS but not for Recursive
(the recursive languages are not recursively enumerable), so it separates CS from Recursive but
does not extend to separating Recursive from RE.
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

/-- **Obligation 1 (uniform computability), now discharged.** The bounded derivation-sequence
search oracle is computable jointly in the grammar-code word and the input word: `decodeCode` is
`Encodable.decode ∘ encode` and `memCode` is the bounded search, primrec via the uniform
`primrec_applyRuleSeq_uniform`. -/
public theorem memOracle_computable [DecidableEq T] [Fintype T] [Primcodable T] :
    Computable (fun p : List T × List T => memOracle p.1 p.2) := by
  have hdec : Primrec (fun u : List T => decodeCode u) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.list_length) (Primrec.const ([], 0))
  exact (memCode_primrec.comp (Primrec.pair (hdec.comp Primrec.fst) Primrec.snd)).to_comp


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

/-- Context-sensitive languages form a strict subclass of recursive languages over
every finite alphabet with at least one symbol.  The finite alphabet supplies the
computability encoding internally, so callers need not choose one. -/
public theorem CS_strict_subclass_Recursive_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  letI : DecidableEq T := Classical.decEq T
  letI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  exact CS_strict_subclass_Recursive
