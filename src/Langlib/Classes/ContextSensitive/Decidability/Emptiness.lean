module

public import Langlib.Classes.ContextSensitive.Decidability.FixedInputTM
public import Langlib.Classes.ContextSensitive.Decidability.Characterization
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Automata.Turing.Equivalence.RecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
public import Langlib.Classes.RecursivelyEnumerable.Examples.NonHalting
public import Langlib.Classes.RecursivelyEnumerable.Closure.Substitution
public import Langlib.Grammars.NonContracting.ErasingImage
public import Langlib.Utilities.ComputabilityPredicates

@[expose]
public section

/-!
# Undecidability of emptiness for context-sensitive grammar codes

The reduction fixes once and for all a finite-state Turing machine recognizing
the unary halting language.  A source program code `c` is represented by a
fixed-input TM grammar for the unary word of length `encode c`.  Padding turns
that unrestricted grammar into a non-contracting grammar, and an epsilon-free
constant homomorphism sends every padded terminal to one chosen target letter.

Crucially, the machine, its rule table, all padding/swap rules, the target
letter, and the finite-nonterminal reindexing are fixed constants.  Only one
start rule varies with `c`, by repeating one fixed encoded cell `encode c`
times.  Thus the construction is a computable map into the concrete subtype
`ContextSensitive.CSCode T`.
-/

open Grammar.ErasingImage Nat.Partrec Turing TMtoGrammarNT

namespace ContextSensitiveEmptiness

/-! ## Finite coding of the fixed TM grammar's nonterminals -/

abbrev TMNTTag (A Λ : Type) :=
  Unit ⊕ (Unit ⊕ ((Option A × Option A) ⊕
    ((Λ × Option A × Option A) ⊕ (Unit ⊕ (Unit ⊕ Option A)))))

def tmntTag {A Λ : Type} :
    TMtoGrammarNT A Λ → TMNTTag A Λ
  | .start => .inl ()
  | .genMore => .inr (.inl ())
  | .cell orig cur => .inr (.inr (.inl (orig, cur)))
  | .headCell q orig cur => .inr (.inr (.inr (.inl (q, orig, cur))))
  | .leftBound => .inr (.inr (.inr (.inr (.inl ()))))
  | .rightBound => .inr (.inr (.inr (.inr (.inr (.inl ())))))
  | .haltCell orig => .inr (.inr (.inr (.inr (.inr (.inr orig)))))

theorem tmntTag_injective {A Λ : Type} :
    Function.Injective (@tmntTag A Λ) := by
  intro x y h
  cases x <;> cases y <;> simp [tmntTag] at h ⊢
  all_goals simp_all

noncomputable instance tmntFintype {A Λ : Type} [Fintype A] [Fintype Λ] :
    Fintype (TMtoGrammarNT A Λ) :=
  Fintype.ofInjective tmntTag tmntTag_injective

/-! ## The padded, collapsed fixed-input grammar -/

variable {A Λ T : Type} [DecidableEq A] [Fintype A]
    [Inhabited Λ] [DecidableEq Λ] [Fintype Λ]

/-- Padding makes the fixed-input unrestricted grammar non-contracting. -/
private noncomputable def paddedGrammar
    (M : Turing.TM0.Machine (Option A) Λ) (input : List A) :
    grammar (Option A) := by
  letI : Fintype (FixedInputTMGrammar.grammarOn M input).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  exact finiteErasingImageGrammar (FixedInputTMGrammar.grammarOn M input)

/-- Send every padded terminal to the same nonempty target word `[letter]`.
The placeholder phase of `hom_grammar` prevents the noninjective relabeling from
creating spurious simulations. -/
private noncomputable def collapsedGrammar
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (input : List A) :
    grammar T :=
  hom_grammar (paddedGrammar M input) (fun _ => [letter])

private theorem collapsedGrammar_context_sensitive
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (input : List A) :
    grammar_context_sensitive (collapsedGrammar letter M input) := by
  letI : Fintype (FixedInputTMGrammar.grammarOn M input).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  apply hom_grammar_context_sensitive
  · intro a
    simp
  · exact grammar_context_sensitive_of_noncontracting _
      (finiteErasingImageGrammar_noncontracting
        (FixedInputTMGrammar.grammarOn M input))

private theorem homomorphicImage_empty_iff {X Y : Type}
    (L : Language X) (h : X → List Y) :
    L.homomorphicImage h = (∅ : Set (List Y)) ↔
      L = (∅ : Set (List X)) := by
  constructor
  · intro himage
    ext w
    constructor
    · intro hw
      have hmem : w.flatMap h ∈ L.homomorphicImage h :=
        (Language.mem_homomorphicImage_iff_flatMap L h _).mpr ⟨w, hw, rfl⟩
      rw [himage] at hmem
      exact hmem.elim
    · exact fun hw => hw.elim
  · intro hempty
    subst L
    ext w
    constructor
    · intro hw
      rw [Language.mem_homomorphicImage_iff_flatMap] at hw
      obtain ⟨x, hx, _⟩ := hw
      exact hx.elim
    · exact fun hw => hw.elim

/-- Neither padding nor the final one-letter homomorphism changes whether the
fixed-input grammar is empty. -/
private theorem collapsedGrammar_empty_iff
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (input : List A) :
    grammar_language (collapsedGrammar letter M input) =
        (∅ : Set (List T)) ↔
      grammar_language (FixedInputTMGrammar.grammarOn M input) =
        (∅ : Set (List A)) := by
  letI : Fintype (FixedInputTMGrammar.grammarOn M input).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  rw [collapsedGrammar, hom_grammar_language_epsfree]
  · rw [homomorphicImage_empty_iff]
    change grammar_language
        (finiteErasingImageGrammar (FixedInputTMGrammar.grammarOn M input)) =
          (∅ : Set (List (Option A))) ↔
      grammar_language (FixedInputTMGrammar.grammarOn M input) =
          (∅ : Set (List A))
    rw [← finiteErasingImageGrammar_language
      (FixedInputTMGrammar.grammarOn M input)]
    exact (homomorphicImage_empty_iff _ erasePadding).symm
  · intro a
    simp

/-! ## Reindex a fixed finite nonterminal type to `Nat` -/

private abbrev FinalNT (A Λ : Type) :=
  Option (Option (TMtoGrammarNT A Λ)) ⊕ Option A

private noncomputable def finalNTPrimcodable (A Λ : Type)
    [Fintype A] [Fintype Λ] : Primcodable (FinalNT A Λ) :=
  Primcodable.ofEquiv (Fin (Fintype.card (FinalNT A Λ)))
    (Fintype.equivFin (FinalNT A Λ))

attribute [local instance] finalNTPrimcodable

/-- Raw `Nat`-nonterminal code obtained by the fixed `Encodable.encode`
embedding. -/
private noncomputable def encodeFiniteGrammar
    (g : grammar T) [Primcodable g.nt] : Code T :=
  (g.rules.map (lift_rule_ Encodable.encode), Encodable.encode g.initial)

private noncomputable def encodedLiftedGrammar
    (g : grammar T) [Primcodable g.nt] : lifted_grammar_ T where
  g₀ := g
  g := ofCode (encodeFiniteGrammar g)
  lift_nt := Encodable.encode
  sink_nt := Encodable.decode₂ g.nt
  lift_inj := Encodable.encode_injective
  sink_inj := by
    intro x y hxy
    cases hx : Encodable.decode₂ g.nt x with
    | none => exact Or.inr rfl
    | some a =>
        left
        have hy : Encodable.decode₂ g.nt y = some a := hxy ▸ hx
        have ex : Encodable.encode a = x := Encodable.decode₂_eq_some.mp hx
        have ey : Encodable.encode a = y := Encodable.decode₂_eq_some.mp hy
        exact ex.symm.trans ey
  lift_nt_sink := Encodable.decode₂_encode
  corresponding_rules := by
    intro r hr
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  preimage_of_rules := by
    rintro r ⟨hr, n, hn⟩
    rcases List.mem_map.mp hr with ⟨r₀, hr₀, rfl⟩
    exact ⟨r₀, hr₀, rfl⟩

private theorem encodeFiniteGrammar_language
    (g : grammar T) [Primcodable g.nt] :
    grammar_language (ofCode (encodeFiniteGrammar g)) =
      grammar_language g := by
  apply Set.eq_of_subset_of_subset
  · intro w hw
    change grammar_derives (ofCode (encodeFiniteGrammar g))
      [symbol.nonterminal (Encodable.encode g.initial)]
      (w.map symbol.terminal) at hw
    have hgood : good_string_ (lg := encodedLiftedGrammar g)
        [symbol.nonterminal (Encodable.encode g.initial)] := by
      intro s hs
      rw [List.mem_singleton] at hs
      subst s
      exact ⟨g.initial, Encodable.decode₂_encode g.initial⟩
    have hsink := sink_deri_ (encodedLiftedGrammar g) hw hgood
    change grammar_derives g [symbol.nonterminal g.initial]
      (w.map symbol.terminal)
    have hterminal := sink_string_map_terminal_
      (Encodable.decode₂ g.nt) w
    change sink_string_ (Encodable.decode₂ g.nt)
      (w.map symbol.terminal) = w.map symbol.terminal at hterminal
    change grammar_derives g
      (sink_string_ (Encodable.decode₂ g.nt)
        [symbol.nonterminal (Encodable.encode g.initial)])
      (sink_string_ (Encodable.decode₂ g.nt)
        (w.map symbol.terminal)) at hsink
    rw [hterminal] at hsink
    simpa [encodedLiftedGrammar, sink_string_, sink_symbol_,
      Encodable.decode₂_encode] using hsink
  · intro w hw
    change grammar_derives g [symbol.nonterminal g.initial]
      (w.map symbol.terminal) at hw
    have hlift := lift_deri_ (encodedLiftedGrammar g) hw
    change grammar_derives (ofCode (encodeFiniteGrammar g))
      [symbol.nonterminal (Encodable.encode g.initial)]
      (w.map symbol.terminal)
    simpa [encodedLiftedGrammar, lift_string_map_terminal_] using hlift

private theorem encodeFiniteGrammar_context_sensitive
    (g : grammar T) [Primcodable g.nt]
    (hg : grammar_context_sensitive g) :
    grammar_context_sensitive
      (ofCode (encodeFiniteGrammar g)) := by
  obtain ⟨hrules, heps⟩ := hg
  constructor
  · intro r' hr'
    rcases List.mem_map.mp hr' with ⟨r, hr, rfl⟩
    rcases hrules r hr with hε | hnc
    · left
      rcases hε with ⟨hL, hN, hR, hO⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [lift_rule_, lift_string_, hL]
      · change Encodable.encode r.input_N = Encodable.encode g.initial
        exact congrArg (fun n : g.nt => Encodable.encode n) hN
      · simp [lift_rule_, lift_string_, hR]
      · simp [lift_rule_, lift_string_, hO]
    · right
      simpa [grule_noncontracting, lift_rule_, lift_string_] using hnc
  · rintro ⟨r', hr', hε'⟩
    rcases List.mem_map.mp hr' with ⟨r, hr, rfl⟩
    have hε : initial_epsilon_rule g r := by
      rcases hε' with ⟨hL, hN, hR, hO⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [lift_rule_, lift_string_] using hL
      · apply Encodable.encode_injective
        simpa [encodeFiniteGrammar, lift_rule_] using hN
      · simpa [lift_rule_, lift_string_] using hR
      · simpa [lift_rule_, lift_string_] using hO
    have hnot := heps ⟨r, hr, hε⟩
    intro r'' hr''
    rcases List.mem_map.mp hr'' with ⟨r₀, hr₀, rfl⟩
    simp only [lift_rule_, lift_string_, List.mem_map, not_exists, not_and]
    rintro s hs hseq
    cases s with
    | terminal t => simp [lift_symbol_] at hseq
    | nonterminal n =>
        have hn : Encodable.encode n = Encodable.encode g.initial := by
          simpa [encodeFiniteGrammar, lift_symbol_] using hseq
        exact hnot r₀ hr₀ (Encodable.encode_injective hn ▸ hs)

/-! ## The only input-dependent encoded rule -/

private theorem paddedStartRule_has_no_terminals
    (w : List A) :
    List.filterMap as_terminal
        (paddedRule (FixedInputTMGrammar.startRule (A := A) (Λ := Λ) w)).output_string =
      [] := by
  cases w <;>
    simp [paddedRule, FixedInputTMGrammar.startRule, liftString, liftSymbol,
      paddingString, paddingSymbol, lift_string_, lift_symbol_, encodeTwoTrack,
      initTwoTrack, as_terminal]

private theorem all_used_terminals_cons {X N : Type}
    (initial : N) (r : grule X N) (rs : List (grule X N)) :
    all_used_terminals
        ({nt := N, initial := initial, rules := r :: rs} : grammar X) =
      List.filterMap as_terminal r.output_string ++
        all_used_terminals
          ({nt := N, initial := initial, rules := rs} : grammar X) := by
  simp [all_used_terminals]

private theorem paddedGrammar_used_terminals_eq_nil
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) :
    all_used_terminals (paddedGrammar M w) =
      all_used_terminals (paddedGrammar M []) := by
  letI : Fintype (tmToGrammar A Λ M).nt := by
    change Fintype (TMtoGrammarNT A Λ)
    infer_instance
  letI : Fintype (FixedInputTMGrammar.grammarOn M w).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  letI : Fintype (FixedInputTMGrammar.grammarOn M []).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  change all_used_terminals
      ({ nt := Option (Option (TMtoGrammarNT A Λ))
         initial := some none
         rules := paddedRule (FixedInputTMGrammar.startRule w) ::
           (List.map paddedRule
              (List.map (lift_rule_ some) (tmToGrammar A Λ M).rules) ++
            swapRules ++ [finishPaddingRule]) } : grammar (Option A)) =
    all_used_terminals
      ({ nt := Option (Option (TMtoGrammarNT A Λ))
         initial := some none
         rules := paddedRule (FixedInputTMGrammar.startRule []) ::
           (List.map paddedRule
              (List.map (lift_rule_ some) (tmToGrammar A Λ M).rules) ++
            swapRules ++ [finishPaddingRule]) } : grammar (Option A))
  rw [all_used_terminals_cons, all_used_terminals_cons,
    paddedStartRule_has_no_terminals, paddedStartRule_has_no_terminals]

section EffectiveStartRule

variable [Primcodable T]

private noncomputable def finalNTSymbol (n : FinalNT A Λ) :
    symbol T Nat :=
  .nonterminal (Encodable.encode n)

private noncomputable def tmNTSymbol (n : TMtoGrammarNT A Λ) :
    symbol T Nat :=
  finalNTSymbol (Sum.inl (some (some n)))

/-- The fully encoded first rule for a unary fixed input.  Its only varying
data are repetitions of the one tape-cell symbol. -/
private noncomputable def encodedUnaryStartRule (a : A) : Nat → grule T Nat
  | 0 =>
      ⟨[], Encodable.encode
          (Sum.inl (some none) : FinalNT A Λ), [],
        [tmNTSymbol (@TMtoGrammarNT.leftBound A Λ),
         tmNTSymbol (@TMtoGrammarNT.headCell A Λ default none none),
         tmNTSymbol (@TMtoGrammarNT.rightBound A Λ)]⟩
  | n + 1 =>
      ⟨[], Encodable.encode
          (Sum.inl (some none) : FinalNT A Λ), [],
        [tmNTSymbol (@TMtoGrammarNT.leftBound A Λ),
         tmNTSymbol (@TMtoGrammarNT.headCell A Λ default (some a) (some a))] ++
          List.replicate n
            (tmNTSymbol (@TMtoGrammarNT.cell A Λ (some a) (some a))) ++
          [tmNTSymbol (@TMtoGrammarNT.rightBound A Λ)]⟩

private theorem encodedUnaryStartRule_primrec (a : A) :
    Primrec (encodedUnaryStartRule (T := T) (Λ := Λ) a) := by
  let inputN : Nat := Encodable.encode
    (Sum.inl (some none) : FinalNT A Λ)
  let lb : symbol T Nat := tmNTSymbol (A := A) (Λ := Λ)
    (@TMtoGrammarNT.leftBound A Λ)
  let blankHead : symbol T Nat := tmNTSymbol (A := A) (Λ := Λ)
    (@TMtoGrammarNT.headCell A Λ default none none)
  let inputHead : symbol T Nat := tmNTSymbol (A := A) (Λ := Λ)
    (@TMtoGrammarNT.headCell A Λ default (some a) (some a))
  let inputCell : symbol T Nat := tmNTSymbol (A := A) (Λ := Λ)
    (@TMtoGrammarNT.cell A Λ (some a) (some a))
  let rb : symbol T Nat := tmNTSymbol (A := A) (Λ := Λ)
    (@TMtoGrammarNT.rightBound A Λ)
  have hrep : Primrec (fun n : Nat => List.replicate n inputCell) := by
    refine (Primrec.list_map Primrec.list_range (Primrec.const inputCell).to₂).of_eq ?_
    intro n
    simp
  have hsucc : Primrec (fun n : Nat =>
      ([lb, inputHead] ++ List.replicate n inputCell ++ [rb] :
        List (symbol T Nat))) := by
    exact Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.const [lb, inputHead]) hrep)
      (Primrec.const [rb])
  have hout : Primrec (fun n : Nat =>
      match n with
      | 0 => ([lb, blankHead, rb] : List (symbol T Nat))
      | k + 1 => [lb, inputHead] ++ List.replicate k inputCell ++ [rb]) := by
    refine (Primrec.nat_casesOn₁ [lb, blankHead, rb] hsucc).of_eq ?_
    intro n
    cases n <;> rfl
  have htuple : Primrec (fun n : Nat =>
      (([] : List (symbol T Nat)), inputN,
        ([] : List (symbol T Nat)),
        match n with
        | 0 => ([lb, blankHead, rb] : List (symbol T Nat))
        | k + 1 => [lb, inputHead] ++ List.replicate k inputCell ++ [rb])) :=
    (Primrec.const ([] : List (symbol T Nat))).pair
      ((Primrec.const inputN).pair
        ((Primrec.const ([] : List (symbol T Nat))).pair hout))
  exact (Primrec.of_equiv_symm.comp htuple).of_eq fun n => by
    cases n <;> rfl

private theorem encodedUnaryStartRule_eq (a : A) (n : Nat) :
    lift_rule_ Encodable.encode
        (@homLiftRule (Option A) T (Option (Option (TMtoGrammarNT A Λ)))
          (paddedRule
            (FixedInputTMGrammar.startRule (A := A) (Λ := Λ)
              (List.replicate n a)))) =
      encodedUnaryStartRule (T := T) (Λ := Λ) a n := by
  cases n with
  | zero =>
    simp [encodedUnaryStartRule, FixedInputTMGrammar.startRule, initTwoTrack,
      encodeTwoTrack, paddedRule, paddingCount, inputLength, paddingString,
      liftString, liftSymbol, homLiftRule, homLiftStr, homLiftSym, lift_rule_,
      lift_string_, lift_symbol_, tmNTSymbol, finalNTSymbol]
  | succ n =>
    change lift_rule_ Encodable.encode
        (@homLiftRule (Option A) T (Option (Option (TMtoGrammarNT A Λ)))
          (paddedRule
            (FixedInputTMGrammar.startRule (A := A) (Λ := Λ)
              (a :: List.replicate n a)))) =
      encodedUnaryStartRule (T := T) (Λ := Λ) a (n + 1)
    simp [encodedUnaryStartRule, FixedInputTMGrammar.startRule, initTwoTrack,
      encodeTwoTrack, paddedRule, paddingCount, inputLength, paddingString,
      liftString, liftSymbol, homLiftRule, homLiftStr, homLiftSym, lift_rule_,
      lift_string_, lift_symbol_, tmNTSymbol, finalNTSymbol]

end EffectiveStartRule

/-! ## A computable raw-code compiler -/

section EffectiveCompiler

variable [Primcodable T]

private theorem collapsedGrammar_rules_cons
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (w : List A) :
    (collapsedGrammar letter M w).rules =
      @homLiftRule (Option A) T (Option (Option (TMtoGrammarNT A Λ)))
          (paddedRule (FixedInputTMGrammar.startRule (A := A) (Λ := Λ) w)) ::
        (collapsedGrammar letter M []).rules.tail := by
  letI : Fintype (tmToGrammar A Λ M).nt := by
    change Fintype (TMtoGrammarNT A Λ)
    infer_instance
  letI : Fintype (FixedInputTMGrammar.grammarOn M w).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  letI : Fintype (FixedInputTMGrammar.grammarOn M []).nt := by
    change Fintype (Option (TMtoGrammarNT A Λ))
    infer_instance
  simp only [collapsedGrammar, hom_grammar]
  rw [show all_used_terminals (paddedGrammar M w) =
      all_used_terminals (paddedGrammar M []) from
    paddedGrammar_used_terminals_eq_nil M w]
  simp [paddedGrammar,
    finiteErasingImageGrammar, FixedInputTMGrammar.grammarOn]

private noncomputable def actualUnaryCode
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) : Code T := by
  letI : Primcodable
      (collapsedGrammar letter M (List.replicate n a)).nt := by
    change Primcodable (FinalNT A Λ)
    infer_instance
  exact encodeFiniteGrammar
    (collapsedGrammar letter M (List.replicate n a))

private noncomputable def encodedUnaryTail
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) :
    List (grule T Nat) := by
  letI : Primcodable (collapsedGrammar letter M []).nt := by
    change Primcodable (FinalNT A Λ)
    infer_instance
  exact (encodeFiniteGrammar (collapsedGrammar letter M [])).1.tail

private noncomputable def encodedUnaryInitial : Nat :=
  Encodable.encode (Sum.inl (some none) : FinalNT A Λ)

/-- Syntactically effective code: a primitive-recursive first rule followed by
one fixed finite tail. -/
private noncomputable def unaryRawCompiler
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (a : A) :
    Nat → Code T :=
  fun n =>
    (encodedUnaryStartRule (T := T) (Λ := Λ) a n ::
      encodedUnaryTail letter M,
     encodedUnaryInitial (A := A) (Λ := Λ))

private theorem unaryRawCompiler_primrec
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (a : A) :
    Primrec (unaryRawCompiler letter M a) := by
  have hrules : Primrec (fun n =>
      encodedUnaryStartRule (T := T) (Λ := Λ) a n ::
        encodedUnaryTail letter M) :=
    Primrec.list_cons.comp
      (encodedUnaryStartRule_primrec (T := T) (Λ := Λ) a)
      (Primrec.const (encodedUnaryTail letter M))
  exact hrules.pair (Primrec.const (encodedUnaryInitial (A := A) (Λ := Λ)))

private theorem actualUnaryCode_initial
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    (actualUnaryCode letter M a n).2 = encodedUnaryInitial (A := A) (Λ := Λ) := by
  simp [actualUnaryCode, encodeFiniteGrammar, collapsedGrammar, hom_grammar,
    paddedGrammar, finiteErasingImageGrammar, FixedInputTMGrammar.grammarOn,
    encodedUnaryInitial]

private theorem actualUnaryCode_rules
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    (actualUnaryCode letter M a n).1 =
      encodedUnaryStartRule (T := T) (Λ := Λ) a n ::
        encodedUnaryTail letter M := by
  simp only [actualUnaryCode, encodeFiniteGrammar]
  rw [collapsedGrammar_rules_cons]
  simp only [List.map_cons]
  rw [encodedUnaryStartRule_eq]
  congr 1

private theorem unaryRawCompiler_eq_actualUnaryCode
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    unaryRawCompiler letter M a n = actualUnaryCode letter M a n := by
  apply Prod.ext
  · exact (actualUnaryCode_rules letter M a n).symm
  · exact (actualUnaryCode_initial letter M a n).symm

end EffectiveCompiler

/-! ## Effective context-sensitive codes and their semantics -/

section CSCompiler

variable [DecidableEq T] [Primcodable T]

private theorem unaryRawCompiler_context_sensitive
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    grammar_context_sensitive (ofCode (unaryRawCompiler letter M a n)) := by
  rw [unaryRawCompiler_eq_actualUnaryCode]
  letI : Primcodable
      (collapsedGrammar letter M (List.replicate n a)).nt := by
    change Primcodable (FinalNT A Λ)
    infer_instance
  simpa [actualUnaryCode] using
    encodeFiniteGrammar_context_sensitive
      (collapsedGrammar letter M (List.replicate n a))
      (collapsedGrammar_context_sensitive letter M (List.replicate n a))

/-- The effective family of concrete context-sensitive grammar codes used in
the halting reduction. -/
private noncomputable def unaryCSCompiler
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (a : A) :
    Nat → ContextSensitive.CSCode T :=
  fun n => ⟨unaryRawCompiler letter M a n,
    unaryRawCompiler_context_sensitive letter M a n⟩

private theorem unaryCSCompiler_primrec
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ) (a : A) :
    Primrec (unaryCSCompiler letter M a) := by
  exact Primrec.subtype_mk
    (hp := ContextSensitive.primrecPred_isCS)
    (unaryRawCompiler_primrec letter M a)

private theorem unaryCSCompiler_language
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    ContextSensitive.contextSensitiveLanguageOf'
        (unaryCSCompiler letter M a n) =
      grammar_language
        (collapsedGrammar letter M (List.replicate n a)) := by
  change contextSensitiveLanguageOf (unaryRawCompiler letter M a n) = _
  rw [ContextSensitive.csLang_eq
    (unaryRawCompiler_context_sensitive letter M a n)]
  rw [unaryRawCompiler_eq_actualUnaryCode]
  letI : Primcodable
      (collapsedGrammar letter M (List.replicate n a)).nt := by
    change Primcodable (FinalNT A Λ)
    infer_instance
  simpa [actualUnaryCode] using
    encodeFiniteGrammar_language
      (collapsedGrammar letter M (List.replicate n a))

private theorem unaryCSCompiler_empty_iff
    (letter : T) (M : Turing.TM0.Machine (Option A) Λ)
    (a : A) (n : Nat) :
    ContextSensitive.contextSensitiveLanguageOf'
        (unaryCSCompiler letter M a n) = (∅ : Set (List T)) ↔
      ¬ (Turing.TM0.eval M
          ((List.replicate n a).map Option.some)).Dom := by
  rw [unaryCSCompiler_language, collapsedGrammar_empty_iff,
    FixedInputTMGrammar.language_empty_iff]

end CSCompiler

/-! ## Undecidability -/

private theorem unaryHaltingInput_eq {Γ : Type} (c : PartrecCode) :
    List.replicate (Encodable.encode c) (Sum.inl () : Unit ⊕ Γ) =
      (codeUnaryWord c).map (fun u => (Sum.inl u : Unit ⊕ Γ)) := by
  simp [codeUnaryWord]

/-- Emptiness is not uniformly decidable for concrete context-sensitive
grammar codes over any nonempty computably encoded alphabet. -/
public theorem contextSensitive_computableEmptiness_undecidable
    {T : Type} [DecidableEq T] [Primcodable T] [Nonempty T] :
    ¬ ComputableEmptiness (CS : Set (Language T))
      (ContextSensitive.contextSensitiveLanguageOf' :
        ContextSensitive.CSCode T → Language T) := by
  intro hEmpty
  have htm : is_TM haltingUnaryLanguage :=
    (is_TM_iff_is_RE haltingUnaryLanguage).2 haltingUnaryLanguage_RE
  obtain ⟨Γ, hΓ, Λ, hΛInhabited, hΛ, M, hM⟩ := htm
  letI : Fintype Γ := hΓ
  letI : Inhabited Λ := hΛInhabited
  letI : Fintype Λ := hΛ
  letI : DecidableEq Γ := Classical.decEq Γ
  letI : DecidableEq Λ := Classical.decEq Λ
  let letter : T := Classical.arbitrary T
  let compiler : PartrecCode → ContextSensitive.CSCode T :=
    fun c => unaryCSCompiler (A := Unit ⊕ Γ) (Λ := Λ)
      letter M (Sum.inl ()) (Encodable.encode c)
  have hCompiler : Computable compiler := by
    exact (unaryCSCompiler_primrec (A := Unit ⊕ Γ) (Λ := Λ)
      letter M (Sum.inl ())).to_comp.comp Primrec.encode.to_comp
  have hCompilerEmpty (c : PartrecCode) :
      ContextSensitive.contextSensitiveLanguageOf' (compiler c) =
          (∅ : Set (List T)) ↔
        ¬ (c.eval 0).Dom := by
    change ContextSensitive.contextSensitiveLanguageOf'
        (unaryCSCompiler (A := Unit ⊕ Γ) (Λ := Λ)
          letter M (Sum.inl ()) (Encodable.encode c)) = _ ↔ _
    rw [unaryCSCompiler_empty_iff]
    rw [unaryHaltingInput_eq]
    simp only [List.map_map]
    change ¬ (Turing.TM0.eval M
        ((codeUnaryWord c).map (fun t => some (Sum.inl t)))).Dom ↔ _
    rw [← hM (codeUnaryWord c), codeUnaryWord_mem_haltingUnaryLanguage]
  have hEmptyPred : ComputablePred (fun sc : ContextSensitive.CSCode T =>
      ContextSensitive.contextSensitiveLanguageOf' sc =
        (∅ : Set (List T))) :=
    hEmpty.2.2.toComputablePred (fun _ => trivial)
  have hCompiledEmpty : ComputablePred (fun c : PartrecCode =>
      ContextSensitive.contextSensitiveLanguageOf' (compiler c) =
        (∅ : Set (List T))) := by
    obtain ⟨f, hf, hspec⟩ := ComputablePred.computable_iff.mp hEmptyPred
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun c => f (compiler c), hf.comp hCompiler, ?_⟩
    funext c
    exact congrFun hspec (compiler c)
  have hNonhalting : ComputablePred (fun c : PartrecCode =>
      ¬ (c.eval 0).Dom) :=
    hCompiledEmpty.of_eq hCompilerEmpty
  apply ComputablePred.halting_problem 0
  exact hNonhalting.not.of_eq fun c => not_not


end ContextSensitiveEmptiness

end
