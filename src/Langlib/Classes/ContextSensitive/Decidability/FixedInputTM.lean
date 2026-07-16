module

public import Langlib.Automata.Turing.Equivalence.TMToGrammar
public import Langlib.Classes.RecursivelyEnumerable.Basics.Lifting
public import Langlib.Grammars.Unrestricted.Toolbox

@[expose]
public section

/-!
# A grammar for one fixed Turing-machine input

The ordinary `tmToGrammar` grammar first guesses an arbitrary input.  For
reductions to grammar emptiness we instead need a grammar whose only possible
initial configuration is a supplied word.  We add a fresh start nonterminal,
make its sole rule produce that configuration, and retain lifted copies of all
the simulation and cleanup rules of `tmToGrammar`.

The machine and its finite alphabets may be fixed noncomputable constants.  The
only varying part of the grammar is the finite word in the fresh start rule.
-/

open Relation Turing TMtoGrammarNT

namespace FixedInputTMGrammar

variable {A Λ : Type} [DecidableEq A] [Fintype A]
    [Inhabited Λ] [DecidableEq Λ] [Fintype Λ]

deriving instance DecidableEq for TMtoGrammarNT

/-- The fresh start rule for a fixed input. -/
public def startRule (w : List A) :
    grule A (Option (TMtoGrammarNT A Λ)) where
  input_L := []
  input_N := none
  input_R := []
  output_string :=
    lift_string_ Option.some
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))

/-- The unrestricted grammar which simulates `M` only on the supplied input
`w`.  `none` is a fresh start nonterminal; all original nonterminals are tagged
with `some`. -/
public noncomputable def grammarOn
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) : grammar A where
  nt := Option (TMtoGrammarNT A Λ)
  initial := none
  rules := startRule w ::
    (tmToGrammar A Λ M).rules.map (lift_rule_ Option.some)

/-- The lifted original grammar sitting below `grammarOn`. -/
private noncomputable def liftedGrammar
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) : lifted_grammar_ A where
  g₀ := tmToGrammar A Λ M
  g := grammarOn M w
  lift_nt := Option.some
  sink_nt := id
  lift_inj := fun _ _ h => Option.some.inj h
  sink_inj := by
    intro x y h
    exact Or.inl h
  lift_nt_sink := by intro n; rfl
  corresponding_rules := by
    intro r hr
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  preimage_of_rules := by
    intro r hr
    rcases hr with ⟨hrules, n, hn⟩
    simp only [grammarOn, List.mem_cons, List.mem_map] at hrules
    rcases hrules with hstart | ⟨r₀, hr₀, hr⟩
    · subst r
      simp [startRule] at hn
    · exact ⟨r₀, hr₀, hr⟩

/-- The fresh start symbol takes exactly one step to the lifted initial
two-track configuration. -/
private theorem start_transform
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) :
    grammar_transforms (grammarOn M w)
      [symbol.nonterminal none]
      (lift_string_ Option.some
        (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))) := by
  refine ⟨startRule w, ?_, [], [], ?_, ?_⟩
  · simp [grammarOn]
  · simp [startRule]
  · simp [startRule]

/-- If `M` halts on `w`, its original TM grammar derives the terminal word
starting directly at the encoded initial configuration. -/
private theorem derives_from_initial_of_halts
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A)
    (h : (Turing.TM0.eval M (w.map Option.some)).Dom) :
    grammar_derives (tmToGrammar A Λ M)
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))
      (w.map symbol.terminal) := by
  obtain ⟨cfg, hreach, hhalt⟩ :
      ∃ cfg : Turing.TM0.Cfg (Option A) Λ,
        Turing.Reaches (Turing.TM0.step M)
            (Turing.TM0.init (w.map some)) cfg ∧
          Turing.TM0.step M cfg = none := by
    rw [TM0.eval, Part.map_Dom, Part.dom_iff_mem] at h
    obtain ⟨cfg, hcfg⟩ := h
    exact ⟨cfg, (Turing.mem_eval.mp hcfg).1, (Turing.mem_eval.mp hcfg).2⟩
  obtain ⟨tc, hsim, htcHalt, hinput⟩ :=
    sim_reaches_halts M
      (initTwoTrack w : @TwoTrackConfig A Λ)
      (Turing.TM0.init (w.map some)) (initCorresponds w)
      cfg hreach hhalt
  rw [extractInput_initTwoTrack] at hinput
  have hcleanup : grammar_derives (tmToGrammar A Λ M)
      (encodeTwoTrack tc)
      ((extractInput (twoTrackOriginals tc)).map symbol.terminal) :=
    (halt_to_halted M tc htcHalt).trans (cleanup_derives M _)
  simpa only [hinput] using hsim.trans hcleanup

/-- Completeness of the fixed-input grammar. -/
private theorem generates_of_halts
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A)
    (h : (Turing.TM0.eval M (w.map Option.some)).Dom) :
    grammar_generates (grammarOn M w) w := by
  have hsource := derives_from_initial_of_halts M w h
  have hlift := lift_deri_ (liftedGrammar M w) hsource
  have hlift' : grammar_derives (grammarOn M w)
      (lift_string_ Option.some
        (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ)))
      (w.map symbol.terminal) := by
    simpa [liftedGrammar, lift_string_map_terminal_] using hlift
  exact (Relation.ReflTransGen.single (start_transform M w)).trans hlift'

/-- A transform out of the fresh start form must use its unique start rule. -/
private theorem first_transform_eq
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A)
    {sf : List (symbol A (grammarOn M w).nt)}
    (h : grammar_transforms (grammarOn M w)
      [symbol.nonterminal none] sf) :
    sf = lift_string_ Option.some
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ)) := by
  obtain ⟨r, hr, u, v, hu, hv⟩ := h
  simp only [grammarOn, List.mem_cons, List.mem_map] at hr
  rcases hr with hstart | ⟨r₀, _hr₀, hr⟩
  · subst r
    have hlen := congrArg List.length hu
    simp [startRule] at hlen
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst u
    subst v
    simpa [startRule] using hv
  · subst r
    have hmem : symbol.nonterminal (some r₀.input_N) ∈
        ([symbol.nonterminal none] :
          List (symbol A (Option (TMtoGrammarNT A Λ)))) := by
      rw [hu]
      simp [lift_rule_]
    simp at hmem

/-- The lifted initial configuration consists entirely of symbols in the image
of `Option.some`, hence is a good input for `sink_deri_`. -/
private theorem initial_good
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) :
    good_string_ (lg := liftedGrammar M w)
      (lift_string_ Option.some
        (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))) := by
  intro s hs
  rw [lift_string_, List.mem_map] at hs
  obtain ⟨s₀, _hs₀, rfl⟩ := hs
  cases s₀ <;> simp [good_letter_, liftedGrammar, lift_symbol_]

/-- Project a derivation after the fresh start step back to the ordinary TM
grammar. -/
private theorem sink_after_start
    (M : Turing.TM0.Machine (Option A) Λ) (w x : List A)
    (h : grammar_derives (grammarOn M w)
      (lift_string_ Option.some
        (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ)))
      (x.map symbol.terminal)) :
    grammar_derives (tmToGrammar A Λ M)
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))
      (x.map symbol.terminal) := by
  have hsink := sink_deri_ (liftedGrammar M w) h (initial_good M w)
  have hroundtrip : ∀ l : List (symbol A (TMtoGrammarNT A Λ)),
      sink_string_ id (lift_string_ Option.some l) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons s l ih =>
        cases s with
        | terminal a =>
            change symbol.terminal a ::
              sink_string_ id (lift_string_ Option.some l) =
                symbol.terminal a :: l
            simp [ih]
        | nonterminal n =>
            change symbol.nonterminal n ::
              sink_string_ id (lift_string_ Option.some l) =
                symbol.nonterminal n :: l
            simp [ih]
  change grammar_derives (tmToGrammar A Λ M)
      (sink_string_ id (lift_string_ Option.some
        (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))))
      (sink_string_ id (x.map symbol.terminal)) at hsink
  rw [hroundtrip,
    sink_string_map_terminal_ (id : Option (TMtoGrammarNT A Λ) →
      Option (TMtoGrammarNT A Λ)) x] at hsink
  exact hsink

/-- Rules usable after the fixed initial configuration preserve the original
input track.  The two input-generating rules are excluded because their input
nonterminals cannot occur in a form without `start` and `genMore`. -/
private def GeneratorFree
    (sf : List (symbol A (TMtoGrammarNT A Λ))) : Prop :=
  ∀ s ∈ sf,
    s ≠ symbol.nonterminal start ∧ s ≠ symbol.nonterminal genMore

/-- A rule whose input is neither generation marker cannot introduce either
generation marker. -/
private theorem rule_output_generatorFree
    (M : Turing.TM0.Machine (Option A) Λ)
    (r : grule A (TMtoGrammarNT A Λ))
    (hr : r ∈ (tmToGrammar A Λ M).rules)
    (hstart : r.input_N ≠ start) (hgen : r.input_N ≠ genMore) :
    GeneratorFree r.output_string := by
  unfold tmToGrammar at hr
  simp only [List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · unfold generationRules at hr
    aesop
  · unfold simulationRules at hr
    rw [List.mem_flatMap] at hr
    obtain ⟨q, _hq, hr⟩ := hr
    rw [List.mem_flatMap] at hr
    obtain ⟨a, _ha, hr⟩ := hr
    rcases hM : M q a with _ | ⟨q', action⟩
    · simp [hM] at hr
    · rcases action with d | b
      · cases d <;>
          simp_all [hM, GeneratorFree, List.mem_append,
            List.mem_flatMap, List.mem_map] <;> aesop
      · simp_all [hM, GeneratorFree, List.mem_append,
          List.mem_flatMap, List.mem_map] <;> aesop
  · unfold cleanupRules at hr
    simp_all [GeneratorFree, List.mem_append, List.mem_flatMap, List.mem_map] <;>
      aesop

/-- One post-generation TM-grammar step preserves absence of generation
markers as well as `terminalContent`. -/
private theorem generatorFree_transform
    (M : Turing.TM0.Machine (Option A) Λ)
    {sf sf' : List (symbol A (TMtoGrammarNT A Λ))}
    (hfree : GeneratorFree sf)
    (hstep : grammar_transforms (tmToGrammar A Λ M) sf sf') :
    GeneratorFree sf' ∧
      terminalContent sf' = terminalContent sf := by
  obtain ⟨r, hr, u, v, hu, hv⟩ := hstep
  have hinput : symbol.nonterminal r.input_N ∈ sf := by
    rw [hu]
    simp
  have hn := hfree _ hinput
  have hnstart : r.input_N ≠ start := by
    intro heq
    exact hn.1 (by simp [heq])
  have hngen : r.input_N ≠ genMore := by
    intro heq
    exact hn.2 (by simp [heq])
  have hout := rule_output_generatorFree M r hr hnstart hngen
  constructor
  · intro s hs
    rw [hv] at hs
    simp only [List.mem_append] at hs
    rcases hs with (hu' | ho) | hv'
    · exact hfree s (by rw [hu]; simp [hu'])
    · exact hout s ho
    · exact hfree s (by rw [hu]; simp [hv'])
  · exact terminalContent_preserved sf sf'
      ⟨r, hr, u, v, hu, hv⟩
      (fun s hs => (hfree s hs).1)
      (fun s hs => (hfree s hs).2)

private theorem terminalContent_eq_of_derives_from_initial
    (M : Turing.TM0.Machine (Option A) Λ) (w x : List A)
    (h : grammar_derives (tmToGrammar A Λ M)
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ))
      (x.map symbol.terminal)) : x = w := by
  have hinit : GeneratorFree
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ)) := by
    intro s hs
    exact ⟨encodeTwoTrack_no_start _ s hs, encodeTwoTrack_no_genMore _ s hs⟩
  have hinvGeneral : ∀ sf : List (symbol A (TMtoGrammarNT A Λ)),
      grammar_derives (tmToGrammar A Λ M)
          (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig A Λ)) sf →
        GeneratorFree sf ∧
          terminalContent (Λ := Λ) sf =
            terminalContent (Λ := Λ) (encodeTwoTrack
              (initTwoTrack w : @TwoTrackConfig A Λ)) := by
    intro sf hd
    induction hd with
    | refl => exact ⟨hinit, rfl⟩
    | tail _ hstep ih =>
        have hs := generatorFree_transform M ih.1 hstep
        exact ⟨hs.1, hs.2.trans ih.2⟩
  have hinv := hinvGeneral
    (x.map (symbol.terminal (N := TMtoGrammarNT A Λ))) h
  simpa [terminalContent_terminal_map, terminalContent_encodeTwoTrack,
    extractInput_initTwoTrack] using hinv.2

/-- Soundness of the fixed-input grammar. -/
private theorem halts_of_generates
    (M : Turing.TM0.Machine (Option A) Λ) (w x : List A)
    (h : grammar_generates (grammarOn M w) x) :
    x = w ∧ (Turing.TM0.eval M (w.map Option.some)).Dom := by
  rcases grammar_tran_or_id_of_deri h with heq | ⟨sf, hfirst, hrest⟩
  · cases x <;> simp at heq
  · have hsf := first_transform_eq M w hfirst
    subst sf
    have hsource := sink_after_start M w x hrest
    have hxw := terminalContent_eq_of_derives_from_initial M w x hsource
    subst x
    exact ⟨rfl, tmToGrammar_halts_of_generates M w
      ((generation_derives M w).trans hsource)⟩

/-- A word belongs to the fixed-input grammar exactly when it is the fixed
input and the machine halts there. -/
public theorem mem_language_iff
    (M : Turing.TM0.Machine (Option A) Λ) (w x : List A) :
    x ∈ grammar_language (grammarOn M w) ↔
      x = w ∧ (Turing.TM0.eval M (w.map Option.some)).Dom := by
  constructor
  · exact halts_of_generates M w x
  · rintro ⟨hx, hhalt⟩
    subst x
    exact generates_of_halts M w hhalt

/-- The fixed-input grammar is empty exactly when the machine does not halt on
that input. -/
public theorem language_empty_iff
    (M : Turing.TM0.Machine (Option A) Λ) (w : List A) :
    grammar_language (grammarOn M w) = (∅ : Set (List A)) ↔
      ¬ (Turing.TM0.eval M (w.map Option.some)).Dom := by
  constructor
  · intro hempty hhalt
    have hw : w ∈ grammar_language (grammarOn M w) :=
      (mem_language_iff M w w).mpr ⟨rfl, hhalt⟩
    rw [hempty] at hw
    exact hw
  · intro hnot
    ext x
    constructor
    · intro hx
      exact (hnot (mem_language_iff M w x |>.mp hx).2).elim
    · exact fun hx => hx.elim

end FixedInputTMGrammar

end
