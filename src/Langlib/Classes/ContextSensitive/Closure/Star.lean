module

public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Utilities.ClosurePredicates
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Classes.RecursivelyEnumerable.Closure.Substitution
import Mathlib.Data.List.SplitBy
import Mathlib.Tactic

/-!
# Context-sensitive closure under Kleene star

The usual fresh-start construction for context-free grammars is not sound for the
noncontracting unrestricted grammars used to define `is_CS`: a rule with a left or
right context could straddle two adjacent copies of the start symbol.  The
construction below prevents this by alternating two colours.  Every symbol of one
simulated copy, terminals included, carries the copy's colour.  Hence a rule of the
source grammar can only act inside one maximal colour run.  After the simulation we
forget the colours by an epsilon-free homomorphism.
-/

variable {T : Type}

namespace ContextSensitiveStar

/-! ## A list localization lemma -/

private lemma monochromatic_infix_append
    {A : Type} (colour : A → Bool)
    {a b p : List A} {ca cb cp : Bool}
    (ha0 : a ≠ []) (hb0 : b ≠ [])
    (ha : ∀ x ∈ a, colour x = ca) (hb : colour (b.head hb0) = cb)
    (hab : ca ≠ cb)
    (hp0 : p ≠ []) (hp : ∀ x ∈ p, colour x = cp)
    (hin : p <:+: a ++ b) :
    p <:+: a ∨ p <:+: b := by
  rcases hin with ⟨u, v, huv⟩
  by_cases hleft : u.length + p.length ≤ a.length
  · left
    have hpre : u ++ p <+: a ++ b := by
      refine ⟨v, ?_⟩
      simpa [List.append_assoc] using huv
    have hprea : u ++ p <+: a :=
      (List.isPrefix_append_of_length (l₁ := u ++ p) (l₂ := a) (l₃ := b)
        (by simpa using hleft)).mp hpre
    rcases hprea with ⟨rest, hrest⟩
    exact ⟨u, rest, by simpa [List.append_assoc] using hrest⟩
  · by_cases hright : a.length ≤ u.length
    · right
      have hpreu : a <+: u := by
        rw [List.prefix_iff_eq_take]
        have htake := congrArg (List.take a.length) huv
        simpa [List.take_append_of_le_length hright] using htake.symm
      rcases hpreu with ⟨u', rfl⟩
      simp only [List.append_assoc, List.append_cancel_left_eq] at huv
      exact ⟨u', v, by simpa [List.append_assoc] using huv⟩
    · exfalso
      have hu_lt : u.length < a.length := Nat.lt_of_not_ge hright
      have ha_lt : a.length < u.length + p.length := Nat.lt_of_not_ge hleft
      have hpreu : u <+: a := by
        rw [List.prefix_iff_eq_take]
        have htake := congrArg (List.take u.length) huv
        simpa [List.take_append_of_le_length hu_lt.le] using htake
      rcases hpreu with ⟨a', rfl⟩
      simp only [List.append_assoc, List.append_cancel_left_eq] at huv
      have ha'0 : a' ≠ [] := by
        intro h
        subst h
        simp at hu_lt
      have ha'_lt : a'.length < p.length := by simp at ha_lt ⊢; omega
      have hprea' : a' <+: p := by
        rw [List.prefix_iff_eq_take]
        have htake := congrArg (List.take a'.length) huv
        simpa [List.take_append_of_le_length ha'_lt.le] using htake.symm
      rcases hprea' with ⟨p', rfl⟩
      have hp'0 : p' ≠ [] := by
        intro h
        subst h
        simp at ha'_lt
      simp only [List.append_assoc, List.append_cancel_left_eq] at huv
      have hp'b : p' <+: b := ⟨v, huv⟩
      have hxmem : a'.getLast ha'0 ∈ a' := List.getLast_mem _
      have hymem : p'.head hp'0 ∈ p' := List.head_mem _
      have hca : colour (a'.getLast ha'0) = ca :=
        ha _ (by simp [hxmem])
      have hcp_left : colour (a'.getLast ha'0) = cp :=
        hp _ (by simp [hxmem])
      have hheads : p'.head hp'0 = b.head hb0 := by
        rcases hp'b with ⟨tail, htail⟩
        cases p' with
        | nil => exact (hp'0 rfl).elim
        | cons z zs =>
            cases b with
            | nil => exact (hb0 rfl).elim
            | cons y ys =>
                simp only [List.cons_append, List.cons.injEq] at htail
                simpa using htail.1
      have hcb : colour (p'.head hp'0) = cb := by rw [hheads]; exact hb
      have hcp_right : colour (p'.head hp'0) = cp :=
        hp _ (by simp [hymem])
      exact hab (hca.symm.trans (hcp_left.trans (hcp_right.symm.trans hcb)))

private def Alternating {A : Type} : List (Bool × List A) → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x.1 ≠ y.1 ∧ Alternating (y :: xs)

private lemma monochromatic_infix_chunks
    {A : Type} (colour : A → Bool)
    {chunks : List (Bool × List A)} {p : List A} {cp : Bool}
    (halt : Alternating chunks)
    (hchunks : ∀ ch ∈ chunks,
      ch.2 ≠ [] ∧ ∀ x ∈ ch.2, colour x = ch.1)
    (hp0 : p ≠ []) (hp : ∀ x ∈ p, colour x = cp)
    (hin : p <:+: (chunks.map Prod.snd).flatten) :
    ∃ ch ∈ chunks, p <:+: ch.2 := by
  induction chunks with
  | nil =>
      simp only [List.map_nil, List.flatten_nil] at hin
      rcases hin with ⟨u, v, huv⟩
      have hup : u ++ p = [] := (List.append_eq_nil_iff.mp huv).1
      have : p = [] := (List.append_eq_nil_iff.mp hup).2
      exact (hp0 this).elim
  | cons ch rest ih =>
      cases rest with
      | nil =>
          refine ⟨ch, by simp, ?_⟩
          simpa using hin
      | cons ch' rest =>
          have hch := hchunks ch (by simp)
          have hch' := hchunks ch' (by simp)
          have hrest0 : ((ch' :: rest).map Prod.snd).flatten ≠ [] := by
            simp [hch'.1]
          have hhead :
              colour (((ch' :: rest).map Prod.snd).flatten.head hrest0) = ch'.1 := by
            simpa [hch'.1] using hch'.2 (ch'.2.head hch'.1) (List.head_mem hch'.1)
          have hne : ch.1 ≠ ch'.1 := halt.1
          have hsplit := monochromatic_infix_append colour hch.1 hrest0
            hch.2 hhead hne hp0 hp (by simpa using hin)
          rcases hsplit with hhere | htail
          · exact ⟨ch, by simp, hhere⟩
          · obtain ⟨found, hfound, hpfound⟩ :=
              ih halt.2 (by
                intro c hc
                exact hchunks c (by simp [hc])) htail
            exact ⟨found, by simp [hfound], hpfound⟩

private lemma monochromatic_occurrence_not_cross
    {A : Type} (colour : A → Bool)
    {a b p u v : List A} {ca cb cp : Bool}
    (ha0 : a ≠ []) (hb0 : b ≠ [])
    (ha : ∀ x ∈ a, colour x = ca)
    (hb : colour (b.head hb0) = cb) (hab : ca ≠ cb)
    (hp0 : p ≠ []) (hp : ∀ x ∈ p, colour x = cp)
    (huv : u ++ p ++ v = a ++ b)
    (hu : u.length < a.length) (hap : a.length < u.length + p.length) : False := by
  have hpreu : u <+: a := by
    rw [List.prefix_iff_eq_take]
    have htake := congrArg (List.take u.length) huv
    simpa [List.take_append_of_le_length hu.le] using htake
  rcases hpreu with ⟨a', rfl⟩
  simp only [List.append_assoc, List.append_cancel_left_eq] at huv
  have ha'0 : a' ≠ [] := by
    intro h
    subst h
    simp at hu
  have ha'_lt : a'.length < p.length := by simp at hap ⊢; omega
  have hprea' : a' <+: p := by
    rw [List.prefix_iff_eq_take]
    have htake := congrArg (List.take a'.length) huv
    simpa [List.take_append_of_le_length ha'_lt.le] using htake.symm
  rcases hprea' with ⟨p', rfl⟩
  have hp'0 : p' ≠ [] := by
    intro h
    subst h
    simp at ha'_lt
  simp only [List.append_assoc, List.append_cancel_left_eq] at huv
  have hp'b : p' <+: b := ⟨v, huv⟩
  have hxmem : a'.getLast ha'0 ∈ a' := List.getLast_mem _
  have hymem : p'.head hp'0 ∈ p' := List.head_mem _
  have hca : colour (a'.getLast ha'0) = ca := ha _ (by simp [hxmem])
  have hcp_left : colour (a'.getLast ha'0) = cp := hp _ (by simp [hxmem])
  have hheads : p'.head hp'0 = b.head hb0 := by
    rcases hp'b with ⟨tail, htail⟩
    cases p' with
    | nil => exact (hp'0 rfl).elim
    | cons z zs =>
        cases b with
        | nil => exact (hb0 rfl).elim
        | cons y ys =>
            simp only [List.cons_append, List.cons.injEq] at htail
            simpa using htail.1
  have hcb : colour (p'.head hp'0) = cb := by rw [hheads]; exact hb
  have hcp_right : colour (p'.head hp'0) = cp := hp _ (by simp [hymem])
  exact hab (hca.symm.trans (hcp_left.trans (hcp_right.symm.trans hcb)))

private lemma locate_monochromatic_occurrence
    {A : Type} (colour : A → Bool)
    {chunks : List (Bool × List A)} {p u v : List A} {cp : Bool}
    (halt : Alternating chunks)
    (hchunks : ∀ ch ∈ chunks,
      ch.2 ≠ [] ∧ ∀ x ∈ ch.2, colour x = ch.1)
    (hp0 : p ≠ []) (hp : ∀ x ∈ p, colour x = cp)
    (huv : u ++ p ++ v = (chunks.map Prod.snd).flatten) :
    ∃ pre ch post left right,
      chunks = pre ++ ch :: post ∧
      ch.2 = left ++ p ++ right ∧
      u = (pre.map Prod.snd).flatten ++ left ∧
      v = right ++ (post.map Prod.snd).flatten := by
  induction chunks generalizing u v with
  | nil =>
      simp only [List.map_nil, List.flatten_nil] at huv
      have hup : u ++ p = [] := (List.append_eq_nil_iff.mp huv).1
      exact (hp0 (List.append_eq_nil_iff.mp hup).2).elim
  | cons ch rest ih =>
      cases rest with
      | nil =>
          refine ⟨[], ch, [], u, v, by simp, ?_, by simp, by simp⟩
          simpa [List.append_assoc] using huv.symm
      | cons ch' rest =>
          let tailChunks := ch' :: rest
          let tailWord := (tailChunks.map Prod.snd).flatten
          have hch := hchunks ch (by simp)
          have hch' := hchunks ch' (by simp)
          have htail0 : tailWord ≠ [] := by
            simp [tailWord, tailChunks, hch'.1]
          have hhead : colour (tailWord.head htail0) = ch'.1 := by
            simpa [tailWord, tailChunks, hch'.1] using
              hch'.2 (ch'.2.head hch'.1) (List.head_mem hch'.1)
          by_cases hleft : u.length + p.length ≤ ch.2.length
          · have hpre : u ++ p <+: ch.2 ++ tailWord := by
              refine ⟨v, ?_⟩
              simpa [List.append_assoc, tailWord, tailChunks] using huv
            have hpreCh : u ++ p <+: ch.2 :=
              (List.isPrefix_append_of_length (l₁ := u ++ p) (l₂ := ch.2)
                (l₃ := tailWord) (by simpa using hleft)).mp hpre
            rcases hpreCh with ⟨right, hright⟩
            have hv : v = right ++ tailWord := by
              have hwhole : u ++ p ++ v = ch.2 ++ tailWord := by
                simpa [tailWord, tailChunks] using huv
              rw [← hright] at hwhole
              simpa [List.append_assoc] using hwhole
            exact ⟨[], ch, tailChunks, u, right, by simp [tailChunks],
              by simpa [List.append_assoc] using hright.symm, by simp,
              by simpa [tailWord] using hv⟩
          · by_cases hright : ch.2.length ≤ u.length
            · have hpreCh : ch.2 <+: u := by
                rw [List.prefix_iff_eq_take]
                have htake := congrArg (List.take ch.2.length) huv
                simpa [List.take_append_of_le_length hright] using htake.symm
              rcases hpreCh with ⟨u', rfl⟩
              have hwhole : ch.2 ++ (u' ++ p ++ v) = ch.2 ++ tailWord := by
                simpa [tailWord, tailChunks, List.append_assoc] using huv
              have huvTail : u' ++ p ++ v = tailWord := List.append_cancel_left hwhole
              obtain ⟨pre, found, post, left, right, htailEq, hfound,
                  hu', hv'⟩ := ih halt.2 (by
                    intro c hc
                    exact hchunks c (by simp [hc])) (by simpa [tailWord] using huvTail)
              refine ⟨ch :: pre, found, post, left, right, ?_, hfound, ?_, hv'⟩
              · simp at htailEq ⊢
                exact htailEq
              · simp [hu', List.append_assoc]
            · exact (monochromatic_occurrence_not_cross colour hch.1 htail0
                hch.2 hhead halt.1 hp0 hp
                (by simpa [tailWord, tailChunks] using huv)
                (Nat.lt_of_not_ge hright) (Nat.lt_of_not_ge hleft)).elim

/-! ## The alternating-copy grammar -/

private abbrev StarNT (N : Type) := (Bool × N) ⊕ Bool

private def tagSym (c : Bool) {N : Type} :
    symbol T N → symbol (Bool × T) (StarNT N)
  | .terminal t => .terminal (c, t)
  | .nonterminal n => .nonterminal (Sum.inl (c, n))

private def generator {N : Type} (c : Bool) :
    symbol (Bool × T) (StarNT N) :=
  .nonterminal (Sum.inr c)

private def taggedColour {N : Type} :
    symbol (Bool × T) (StarNT N) → Bool
  | .terminal x => x.1
  | .nonterminal (.inl x) => x.1
  | .nonterminal (.inr c) => c

@[simp] private lemma taggedColour_tagSym (c : Bool) (s : symbol T N) :
    taggedColour (tagSym c s) = c := by cases s <;> rfl

@[simp] private lemma taggedColour_generator (c : Bool) :
    taggedColour (@generator T N c) = c := rfl

private def tagRule (c : Bool) {N : Type} (r : grule T N) :
    grule (Bool × T) (StarNT N) where
  input_L := r.input_L.map (tagSym c)
  input_N := Sum.inl (c, r.input_N)
  input_R := r.input_R.map (tagSym c)
  output_string := r.output_string.map (tagSym c)

private def continueRule (g : grammar T) (c : Bool) :
    grule (Bool × T) (StarNT g.nt) :=
  ⟨[], Sum.inr c, [],
    [tagSym c (.nonterminal g.initial), generator (!c)]⟩

private def stopRule (g : grammar T) (c : Bool) :
    grule (Bool × T) (StarNT g.nt) :=
  ⟨[], Sum.inr c, [], [tagSym c (.nonterminal g.initial)]⟩

private def alternatingGrammar (g : grammar T) : grammar (Bool × T) where
  nt := StarNT g.nt
  initial := Sum.inr false
  rules := [continueRule g false, stopRule g false,
      continueRule g true, stopRule g true] ++
    g.rules.flatMap fun r => [tagRule false r, tagRule true r]

private lemma tagRule_mem (g : grammar T) {r : grule T g.nt}
    (hr : r ∈ g.rules) (c : Bool) :
    tagRule c r ∈ (alternatingGrammar g).rules := by
  simp only [alternatingGrammar, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact Or.inr ⟨r, hr, by cases c <;> simp⟩

private lemma continueRule_mem (g : grammar T) (c : Bool) :
    continueRule g c ∈ (alternatingGrammar g).rules := by
  cases c <;> simp [alternatingGrammar]

private lemma stopRule_mem (g : grammar T) (c : Bool) :
    stopRule g c ∈ (alternatingGrammar g).rules := by
  cases c <;> simp [alternatingGrammar]

private lemma alternatingGrammar_noncontracting (g : grammar T)
    (hg : grammar_noncontracting g) :
    grammar_noncontracting (alternatingGrammar g) := by
  intro r hr
  simp only [alternatingGrammar, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | ⟨r₀, hr₀, hr⟩
  · simp [continueRule]
  · simp [stopRule]
  · simp [continueRule]
  · simp [stopRule]
  · rcases hr with rfl | rfl
    · simpa [tagRule, List.length_map] using hg r₀ hr₀
    · simpa [tagRule, List.length_map] using hg r₀ hr₀

private lemma tag_transforms (g : grammar T) (c : Bool)
    {x y : List (symbol T g.nt)} (h : grammar_transforms g x y) :
    grammar_transforms (alternatingGrammar g)
      (x.map (tagSym c)) (y.map (tagSym c)) := by
  rcases h with ⟨r, hr, u, v, rfl, rfl⟩
  refine ⟨tagRule c r, tagRule_mem g hr c, u.map (tagSym c), v.map (tagSym c), ?_, ?_⟩
  · simp [tagRule, tagSym, List.map_append, List.append_assoc]
  · simp [tagRule, List.map_append, List.append_assoc]

private lemma tag_derives (g : grammar T) (c : Bool)
    {x y : List (symbol T g.nt)} (h : grammar_derives g x y) :
    grammar_derives (alternatingGrammar g)
      (x.map (tagSym c)) (y.map (tagSym c)) := by
  induction h with
  | refl => exact grammar_deri_self
  | tail _ hs ih => exact grammar_deri_of_deri_tran ih (tag_transforms g c hs)

private def startForms (g : grammar T) : Bool → List (List T) →
    List (symbol (Bool × T) (alternatingGrammar g).nt)
  | _, [] => []
  | c, _ :: ws => tagSym c (.nonterminal g.initial) :: startForms g (!c) ws

private def taggedWords : Bool → List (List T) → List (Bool × T)
  | _, [] => []
  | c, w :: ws => w.map (c, ·) ++ taggedWords (!c) ws

private lemma generator_derives_startForms (g : grammar T) (c : Bool)
    {ws : List (List T)} (hws : ws ≠ []) :
    grammar_derives (alternatingGrammar g) [generator c] (startForms g c ws) := by
  cases ws with
  | nil => contradiction
  | cons w ws =>
      cases ws with
      | nil =>
          apply grammar_deri_of_tran
          exact ⟨stopRule g c, stopRule_mem g c, [], [], by simp [stopRule, generator],
            by simp [stopRule, startForms]⟩
      | cons w' ws =>
          have hstep : grammar_transforms (alternatingGrammar g) [generator c]
              [tagSym c (.nonterminal g.initial), generator (!c)] :=
            ⟨continueRule g c, continueRule_mem g c, [], [], by simp [continueRule, generator],
              by simp [continueRule]⟩
          have htail := generator_derives_startForms g (!c)
            (ws := w' :: ws) (by simp)
          exact grammar_deri_of_tran_deri hstep
            (by simpa [startForms] using
              grammar_deri_with_prefix [tagSym c (.nonterminal g.initial)] htail)

private lemma startForms_derives_taggedWords (g : grammar T) (c : Bool)
    {ws : List (List T)}
    (hws : ∀ w ∈ ws, w ∈ grammar_language g) :
    grammar_derives (alternatingGrammar g) (startForms g c ws)
      ((taggedWords c ws).map symbol.terminal) := by
  induction ws generalizing c with
  | nil => exact grammar_deri_self
  | cons w ws ih =>
      have hw : grammar_derives g [symbol.nonterminal g.initial]
          (w.map symbol.terminal) := hws w (by simp)
      have htag := tag_derives g c hw
      have hfirst : grammar_derives (alternatingGrammar g)
          ([tagSym c (.nonterminal g.initial)] ++ startForms g (!c) ws)
          ((w.map (fun t => symbol.terminal (c, t))) ++ startForms g (!c) ws) := by
        convert grammar_deri_with_postfix (startForms g (!c) ws) htag using 1 <;>
          simp [List.map_map, Function.comp_def, tagSym]
      have hrest := ih (!c) (fun x hx => hws x (by simp [hx]))
      have hsecond := grammar_deri_with_prefix
        (w.map (fun t => symbol.terminal (c, t))) hrest
      exact grammar_deri_of_deri_deri hfirst (by simpa [taggedWords] using hsecond)

private lemma alternatingGrammar_complete (g : grammar T)
    {ws : List (List T)} (hws0 : ws ≠ [])
    (hws : ∀ w ∈ ws, w ∈ grammar_language g) :
    taggedWords false ws ∈ grammar_language (alternatingGrammar g) := by
  exact grammar_deri_of_deri_deri (generator_derives_startForms g false hws0)
    (startForms_derives_taggedWords g false hws)

/-! ## Soundness invariant -/

private lemma tagSym_injective (c : Bool) :
    Function.Injective (@tagSym T c N) := by
  intro x y h
  cases x <;> cases y <;> simp [tagSym] at h <;> simp [h]

private def lhsString (r : grule T N) : List (symbol T N) :=
  r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R

private lemma tagRule_lhs (c : Bool) (r : grule T N) :
    (tagRule c r).input_L ++ [symbol.nonterminal (tagRule c r).input_N] ++
        (tagRule c r).input_R =
      (lhsString r).map (tagSym c) := by
  simp [tagRule, lhsString, tagSym, List.map_append, List.append_assoc]

private lemma source_chunk_step (g : grammar T) (hg : grammar_noncontracting g)
    (c : Bool) {r : grule T g.nt} (hr : r ∈ g.rules)
    {s : List (symbol T g.nt)}
    {left right : List (symbol (Bool × T) (StarNT g.nt))}
    (hs0 : s ≠ [])
    (hs : grammar_derives g [symbol.nonterminal g.initial] s)
    (hshape : s.map (tagSym c) =
      left ++ (lhsString r).map (tagSym c) ++ right) :
    ∃ s', s' ≠ [] ∧
      grammar_derives g [symbol.nonterminal g.initial] s' ∧
      s'.map (tagSym c) =
        left ++ r.output_string.map (tagSym c) ++ right := by
  let left₀ := s.take left.length
  let right₀ := s.drop (left.length + (lhsString r).length)
  have hleft : left₀.map (tagSym c) = left := by
    have h := congrArg (List.take left.length) hshape
    simpa [left₀, List.map_take] using h
  have hright : right₀.map (tagSym c) = right := by
    have h₁ := congrArg (List.drop left.length) hshape
    have h₁' : (s.map (tagSym c)).drop left.length =
        (lhsString r).map (tagSym c) ++ right := by
      simpa using h₁
    have h₂ := congrArg (List.drop (lhsString r).length) h₁'
    simpa [right₀, List.map_drop, List.drop_drop, Nat.add_comm] using h₂
  have hsource : s = left₀ ++ lhsString r ++ right₀ := by
    apply (tagSym_injective c).list_map
    simp [List.map_append, hleft, hright, hshape]
  let s' := left₀ ++ r.output_string ++ right₀
  have hstep : grammar_transforms g s s' := by
    refine ⟨r, hr, left₀, right₀, ?_, rfl⟩
    simpa [lhsString, List.append_assoc] using hsource
  have hs' := grammar_deri_of_deri_tran hs hstep
  have hs'0 : s' ≠ [] := by
    intro hnil
    have hlen := noncontracting_transforms_length_le g hg hstep
    rw [hnil] at hlen
    simp at hlen
    exact hs0 hlen
  refine ⟨s', hs'0, hs', ?_⟩
  simp [s', List.map_append, hleft, hright]

private def SourceChunk (g : grammar T)
    (ch : Bool × List (symbol (Bool × T) (alternatingGrammar g).nt)) : Prop :=
  ∃ s : List (symbol T g.nt),
    s ≠ [] ∧ grammar_derives g [symbol.nonterminal g.initial] s ∧
      ch.2 = s.map (tagSym ch.1)

private def generatorChunk (g : grammar T) (c : Bool) :
    Bool × List (symbol (Bool × T) (StarNT g.nt)) :=
  (c, [generator c])

private def renderChunks
    (chunks : List (Bool × List A)) : List A :=
  (chunks.map Prod.snd).flatten

private def GoodForm (g : grammar T)
    (sf : List (symbol (Bool × T) (alternatingGrammar g).nt)) : Prop :=
  (∃ chunks,
      Alternating chunks ∧ (∀ ch ∈ chunks, SourceChunk g ch) ∧
      sf = renderChunks chunks) ∨
  (∃ chunks c,
      Alternating (chunks ++ [generatorChunk g c]) ∧
      (∀ ch ∈ chunks, SourceChunk g ch) ∧
      sf = renderChunks (chunks ++ [generatorChunk g c]))

private lemma sourceChunk_properties {g : grammar T} {ch}
    (h : SourceChunk g ch) :
    ch.2 ≠ [] ∧ ∀ x ∈ ch.2, taggedColour x = ch.1 := by
  rcases h with ⟨s, hs0, _hs, hshape⟩
  rw [hshape]
  constructor
  · simpa using hs0
  · intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    simp

private lemma generatorChunk_properties (g : grammar T) (c : Bool) :
    (generatorChunk g c).2 ≠ [] ∧
      ∀ x ∈ (generatorChunk g c).2, taggedColour x = c := by
  simp [generatorChunk]

private lemma generator_not_mem_sourceChunk {g : grammar T} {ch}
    (h : SourceChunk g ch) (c : Bool) : generator c ∉ ch.2 := by
  rcases h with ⟨s, _hs0, _hs, hshape⟩
  rw [hshape]
  simp only [List.mem_map]
  rintro ⟨x, _hx, hx⟩
  cases x <;> simp [tagSym, generator] at hx

private lemma tagged_nonterminal_not_generator (c : Bool) (n : N) (d : Bool) :
    tagSym c (symbol.nonterminal n) ≠ @generator T N d := by
  simp [tagSym, generator]

private lemma goodForm_initial (g : grammar T) :
    GoodForm g [symbol.nonterminal (alternatingGrammar g).initial] := by
  right
  refine ⟨[], false, by simp [Alternating, generatorChunk], by simp, ?_⟩
  simp [alternatingGrammar, renderChunks, generatorChunk, generator]

private lemma alternating_replace_snd
    {A : Type} {pre post : List (Bool × List A)} {old new : Bool × List A}
    (h : Alternating (pre ++ old :: post)) (hc : new.1 = old.1) :
    Alternating (pre ++ new :: post) := by
  induction pre with
  | nil =>
      cases post with
      | nil => simp [Alternating]
      | cons x xs => simpa [Alternating, hc] using h
  | cons x pre ih =>
      cases pre with
      | nil =>
          cases post with
          | nil => simpa [Alternating, hc] using h
          | cons y ys => simpa [Alternating, hc] using h
      | cons y ys =>
          simp only [List.cons_append, Alternating] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma append_singleton_eq_append_cons_of_not_mem
    {A : Type} {x : A} {pref u v : List A}
    (hx : x ∉ pref) (h : pref ++ [x] = u ++ x :: v) :
    u = pref ∧ v = [] := by
  induction pref generalizing u with
  | nil =>
      cases u with
      | nil => simp at h ⊢; exact h
      | cons y ys => simp at h
  | cons a tail ih =>
      have hax : a ≠ x := by
        intro hax
        subst a
        exact hx (by simp)
      have hxtail : x ∉ tail := by
        intro hmem
        exact hx (by simp [hmem])
      cases u with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact absurd h.1 hax
      | cons b u =>
          simp only [List.cons_append, List.cons.injEq] at h
          have htail := ih hxtail h.2
          exact ⟨by rw [← h.1]; simp [htail.1], htail.2⟩

private lemma generator_not_mem_render {g : grammar T} {chunks}
    (hs : ∀ ch ∈ chunks, SourceChunk g ch) (c : Bool) :
    generator c ∉ renderChunks chunks := by
  intro hmem
  simp only [renderChunks, List.mem_flatten, List.mem_map] at hmem
  rcases hmem with ⟨l, ⟨ch, hch, rfl⟩, hgen⟩
  exact generator_not_mem_sourceChunk (hs ch hch) c hgen

private lemma replace_preserves_final_generator
    {A : Type} {base pre post : List (Bool × List A)}
    {gen old new : Bool × List A}
    (hEq : base ++ [gen] = pre ++ old :: post) (hne : old ≠ gen) :
    ∃ base', base = pre ++ old :: post.dropLast ∧
      base' = pre ++ new :: post.dropLast ∧
      pre ++ new :: post = base' ++ [gen] := by
  have hpost : post ≠ [] := by
    intro hp
    subst post
    have hlast := congrArg List.getLast? hEq
    simp at hlast
    exact hne hlast.symm
  have hlast : post.getLast hpost = gen := by
    have hlast? : some gen = post.getLast? := calc
      some gen = (base ++ [gen]).getLast? := by simp
      _ = (pre ++ old :: post).getLast? := congrArg List.getLast? hEq
      _ = post.getLast? := by
        rw [show pre ++ old :: post = (pre ++ [old]) ++ post by simp]
        exact List.getLast?_append_of_ne_nil _ hpost
    rw [List.getLast?_eq_getLast_of_ne_nil hpost] at hlast?
    exact Option.some.inj hlast?.symm
  have hpostEq : post = post.dropLast ++ [gen] := by
    rw [← hlast]
    exact (List.dropLast_append_getLast hpost).symm
  have hbase : base = pre ++ old :: post.dropLast := by
    have hEq' : base ++ [gen] = (pre ++ old :: post.dropLast) ++ [gen] := by
      rw [hEq, hpostEq]
      simp [List.append_assoc]
    exact List.append_cancel_right hEq'
  refine ⟨pre ++ new :: post.dropLast, hbase, rfl, ?_⟩
  calc
    pre ++ new :: post = pre ++ new :: (post.dropLast ++ [gen]) :=
      congrArg (fun z => pre ++ new :: z) hpostEq
    _ = (pre ++ new :: post.dropLast) ++ [gen] := by simp [List.append_assoc]

private lemma replace_located_source_chunk
    (g : grammar T) (hg : grammar_noncontracting g)
    (c : Bool) {r : grule T g.nt} (hr : r ∈ g.rules)
    {chunks : List (Bool × List (symbol (Bool × T) (StarNT g.nt)))}
    {u v : List (symbol (Bool × T) (StarNT g.nt))}
    (halt : Alternating chunks)
    (hchunkProps : ∀ ch ∈ chunks,
      ch.2 ≠ [] ∧ ∀ x ∈ ch.2, taggedColour x = ch.1)
    (huv : u ++ (lhsString r).map (tagSym c) ++ v = renderChunks chunks)
    (hsource : ∀ ch ∈ chunks, ch.2 ≠ [generator ch.1] → SourceChunk g ch) :
    ∃ chunks',
      Alternating chunks' ∧
      (∀ ch ∈ chunks', ch.2 ≠ [generator ch.1] → SourceChunk g ch) ∧
      u ++ r.output_string.map (tagSym c) ++ v = renderChunks chunks' ∧
      (∀ ch ∈ chunks', ch.2 = [generator ch.1] → ch ∈ chunks) ∧
      (∀ base d, chunks = base ++ [generatorChunk g d] →
        (∀ ch ∈ base, SourceChunk g ch) →
        ∃ base', chunks' = base' ++ [generatorChunk g d] ∧
          ∀ ch ∈ base', SourceChunk g ch) := by
  have hp0 : (lhsString r).map (tagSym c) ≠ [] := by
    simp [lhsString]
  have hpcol : ∀ x ∈ (lhsString r).map (tagSym c), taggedColour x = c := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨s, _hs, rfl⟩
    simp
  obtain ⟨pre, found, post, left, right, hchunks, hfound, hu, hv⟩ :=
    locate_monochromatic_occurrence taggedColour halt hchunkProps hp0 hpcol huv
  have hfoundNotGen : found.2 ≠ [generator found.1] := by
    intro heq
    have hnt : tagSym c (symbol.nonterminal r.input_N) ∈ found.2 := by
      rw [hfound]
      simp [lhsString]
    rw [heq] at hnt
    simp [tagSym, generator] at hnt
  have hfoundSource : SourceChunk g found :=
    hsource found (by rw [hchunks]; simp) hfoundNotGen
  have hcolour : found.1 = c := by
    have hz : tagSym c (symbol.nonterminal r.input_N) ∈ found.2 := by
      rw [hfound]
      simp [lhsString]
    have hcFound := (sourceChunk_properties hfoundSource).2 _ hz
    simpa using hcFound.symm
  rcases hfoundSource with ⟨s, hs0, hs, hsShape⟩
  have hshape : s.map (tagSym c) =
      left ++ (lhsString r).map (tagSym c) ++ right := by
    rw [hcolour] at hsShape
    exact hsShape.symm.trans hfound
  obtain ⟨s', hs'0, hs', hs'Shape⟩ :=
    source_chunk_step g hg c hr hs0 hs hshape
  let newChunk : Bool × List (symbol (Bool × T) (StarNT g.nt)) :=
    (found.1, left ++ r.output_string.map (tagSym c) ++ right)
  let chunks' := pre ++ newChunk :: post
  have hnewSource : SourceChunk g newChunk := by
    refine ⟨s', hs'0, hs', ?_⟩
    simp only [newChunk]
    rw [hcolour]
    exact hs'Shape.symm
  have halt' : Alternating chunks' := by
    apply alternating_replace_snd (by simpa [hchunks] using halt)
    rfl
  have hsources' :
      ∀ ch ∈ chunks', ch.2 ≠ [generator ch.1] → SourceChunk g ch := by
    intro ch hch _hnot
    simp only [chunks', List.mem_append, List.mem_cons] at hch
    rcases hch with hpre | rfl | hpost
    · exact hsource ch (by rw [hchunks]; simp [hpre]) _hnot
    · exact hnewSource
    · exact hsource ch (by rw [hchunks]; simp [hpost]) _hnot
  have hrender :
      u ++ r.output_string.map (tagSym c) ++ v = renderChunks chunks' := by
    rw [hu, hv]
    simp [chunks', newChunk, renderChunks, List.map_append, List.flatten_append,
      List.append_assoc]
  have hgenOld : ∀ ch ∈ chunks', ch.2 = [generator ch.1] → ch ∈ chunks := by
    intro ch hch hgen
    simp only [chunks', List.mem_append, List.mem_cons] at hch
    rcases hch with hpre | rfl | hpost
    · rw [hchunks]; simp [hpre]
    · exact False.elim (generator_not_mem_sourceChunk hnewSource newChunk.1
        (by rw [hgen]; simp))
    · rw [hchunks]; simp [hpost]
  refine ⟨chunks', halt', hsources', hrender, hgenOld, ?_⟩
  intro base d hlast hbaseSource
  have hfoundNeLast : found ≠ generatorChunk g d := by
    intro heq
    subst found
    exact hfoundNotGen (by simp [generatorChunk])
  have hEqLast : base ++ [generatorChunk g d] = pre ++ found :: post :=
    hlast.symm.trans hchunks
  obtain ⟨base', hbaseOld, hbaseDef, hbase'⟩ := replace_preserves_final_generator
    (base := base) (pre := pre) (post := post)
    (gen := generatorChunk g d) (old := found) (new := newChunk)
    hEqLast hfoundNeLast
  refine ⟨base', by simpa [chunks'] using hbase', ?_⟩
  intro ch hch
  rw [hbaseDef] at hch
  simp only [List.mem_append, List.mem_cons] at hch
  rcases hch with hpre | rfl | hpost
  · exact hbaseSource ch (by rw [hbaseOld]; simp [hpre])
  · exact hnewSource
  · apply hbaseSource ch
    rw [hbaseOld]
    simpa only [List.mem_append, List.mem_cons] using
      (Or.inr (Or.inr hpost) : ch ∈ pre ∨ ch = found ∨ ch ∈ post.dropLast)

private lemma goodForm_tagRule_step
    (g : grammar T) (hg : grammar_noncontracting g)
    (c : Bool) {r : grule T g.nt} (hr : r ∈ g.rules)
    {before after u v : List (symbol (Bool × T) (StarNT g.nt))}
    (hgood : GoodForm g before)
    (hbefore : before = u ++ (tagRule c r).input_L ++
      [symbol.nonterminal (tagRule c r).input_N] ++ (tagRule c r).input_R ++ v)
    (hafter : after = u ++ (tagRule c r).output_string ++ v) :
    GoodForm g after := by
  have hbefore' : before = u ++ (lhsString r).map (tagSym c) ++ v := by
    rw [← tagRule_lhs c r]
    simpa [List.append_assoc] using hbefore
  have hafter' : after = u ++ r.output_string.map (tagSym c) ++ v := by
    simpa [tagRule] using hafter
  rcases hgood with ⟨chunks, halt, hsources, hform⟩ |
      ⟨chunks, d, halt, hsources, hform⟩
  · have hprops : ∀ ch ∈ chunks,
        ch.2 ≠ [] ∧ ∀ x ∈ ch.2, taggedColour x = ch.1 :=
      fun ch hch => sourceChunk_properties (hsources ch hch)
    have huv : u ++ (lhsString r).map (tagSym c) ++ v = renderChunks chunks :=
      hbefore'.symm.trans hform
    obtain ⟨chunks', halt', hsources', hrender, hgenOld, _hlast⟩ :=
      replace_located_source_chunk g hg c hr halt hprops huv
        (fun ch hch _ => hsources ch hch)
    left
    refine ⟨chunks', halt', ?_, hafter'.trans hrender⟩
    intro ch hch
    by_cases hgen : ch.2 = [generator ch.1]
    · exact hsources ch (hgenOld ch hch hgen)
    · exact hsources' ch hch hgen
  · let allChunks := chunks ++ [generatorChunk g d]
    have hprops : ∀ ch ∈ allChunks,
        ch.2 ≠ [] ∧ ∀ x ∈ ch.2, taggedColour x = ch.1 := by
      intro ch hch
      simp only [allChunks, List.mem_append, List.mem_singleton] at hch
      rcases hch with hbase | rfl
      · exact sourceChunk_properties (hsources ch hbase)
      · exact generatorChunk_properties g d
    have huv : u ++ (lhsString r).map (tagSym c) ++ v = renderChunks allChunks :=
      hbefore'.symm.trans hform
    have hkind : ∀ ch ∈ allChunks,
        ch.2 ≠ [generator ch.1] → SourceChunk g ch := by
      intro ch hch hnot
      simp only [allChunks, List.mem_append, List.mem_singleton] at hch
      rcases hch with hbase | rfl
      · exact hsources ch hbase
      · exact False.elim (hnot (by simp [generatorChunk]))
    obtain ⟨allChunks', halt', _hsources', hrender, _hgenOld, hlast⟩ :=
      replace_located_source_chunk g hg c hr halt hprops huv hkind
    obtain ⟨base', hdecomp, hbaseSources⟩ :=
      hlast chunks d rfl hsources
    right
    refine ⟨base', d, ?_, hbaseSources, ?_⟩
    · simpa [hdecomp] using halt'
    · rw [← hdecomp]
      exact hafter'.trans hrender

private lemma alternating_append_opposite
    {A : Type} {chunks : List (Bool × List A)}
    {last next : Bool × List A}
    (h : Alternating (chunks ++ [last])) (hne : last.1 ≠ next.1) :
    Alternating (chunks ++ [last, next]) := by
  induction chunks with
  | nil => simpa [Alternating] using hne
  | cons x chunks ih =>
      cases chunks with
      | nil =>
          have hx : x.1 ≠ last.1 := by simpa [Alternating] using h
          simpa [Alternating] using And.intro hx hne
      | cons y ys =>
          simp only [List.cons_append, Alternating] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma locate_generator_in_goodForm
    (g : grammar T) (c : Bool)
    {before u v : List (symbol (Bool × T) (StarNT g.nt))}
    (hgood : GoodForm g before)
    (hbefore : before = u ++ [generator c] ++ v) :
    ∃ chunks,
      Alternating (chunks ++ [generatorChunk g c]) ∧
      (∀ ch ∈ chunks, SourceChunk g ch) ∧
      u = renderChunks chunks ∧ v = [] := by
  rcases hgood with ⟨chunks, _halt, hsources, hform⟩ |
      ⟨chunks, d, halt, hsources, hform⟩
  · have hmem : generator c ∈ renderChunks chunks := by
      rw [← hform, hbefore]
      simp
    exact False.elim (generator_not_mem_render hsources c hmem)
  · have hEq : renderChunks chunks ++ [generator d] =
        u ++ generator c :: v := by
      have := hform.symm.trans hbefore
      simpa [renderChunks, generatorChunk, List.map_append, List.flatten_append,
        List.append_assoc] using this
    have hcd : c = d := by
      have hmem : generator c ∈ renderChunks chunks ++ [generator d] := by
        rw [hEq]
        simp
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hbase | heq
      · exact False.elim (generator_not_mem_render hsources c hbase)
      · simpa [generator] using congrArg (fun x => match x with
            | symbol.nonterminal (Sum.inr b) => b
            | _ => c) heq
    subst d
    have hpos := append_singleton_eq_append_cons_of_not_mem
      (generator_not_mem_render hsources c) hEq
    exact ⟨chunks, halt, hsources, hpos.1, hpos.2⟩

private def initialChunk (g : grammar T) (c : Bool) :
    Bool × List (symbol (Bool × T) (StarNT g.nt)) :=
  (c, [tagSym c (.nonterminal g.initial)])

private lemma initialChunk_source (g : grammar T) (c : Bool) :
    SourceChunk g (initialChunk g c) := by
  refine ⟨[.nonterminal g.initial], by simp, grammar_deri_self, ?_⟩
  simp [initialChunk]

private lemma goodForm_continue_step
    (g : grammar T) (c : Bool)
    {before after u v : List (symbol (Bool × T) (StarNT g.nt))}
    (hgood : GoodForm g before)
    (hbefore : before = u ++ [generator c] ++ v)
    (hafter : after = u ++
      [tagSym c (.nonterminal g.initial), generator (!c)] ++ v) :
    GoodForm g after := by
  obtain ⟨chunks, halt, hsources, hu, hv⟩ :=
    locate_generator_in_goodForm g c hgood hbefore
  let newBase := chunks ++ [initialChunk g c]
  right
  refine ⟨newBase, !c, ?_, ?_, ?_⟩
  · have hbaseAlt : Alternating newBase := by
      apply alternating_replace_snd (pre := chunks) (post := []) halt
      rfl
    simpa [newBase, List.append_assoc] using
      (alternating_append_opposite hbaseAlt
        (next := generatorChunk g (!c)) (by simp [initialChunk, generatorChunk]))
  · intro ch hch
    simp only [newBase, List.mem_append, List.mem_singleton] at hch
    rcases hch with h | rfl
    · exact hsources ch h
    · exact initialChunk_source g c
  · rw [hafter, hu, hv]
    simp [newBase, initialChunk, renderChunks, generatorChunk, List.map_append,
      List.flatten_append, List.append_assoc]
    rfl

private lemma goodForm_stop_step
    (g : grammar T) (c : Bool)
    {before after u v : List (symbol (Bool × T) (StarNT g.nt))}
    (hgood : GoodForm g before)
    (hbefore : before = u ++ [generator c] ++ v)
    (hafter : after = u ++ [tagSym c (.nonterminal g.initial)] ++ v) :
    GoodForm g after := by
  obtain ⟨chunks, halt, hsources, hu, hv⟩ :=
    locate_generator_in_goodForm g c hgood hbefore
  left
  refine ⟨chunks ++ [initialChunk g c], ?_, ?_, ?_⟩
  · apply alternating_replace_snd (pre := chunks) (post := []) halt
    rfl
  · intro ch hch
    simp only [List.mem_append, List.mem_singleton] at hch
    rcases hch with h | rfl
    · exact hsources ch h
    · exact initialChunk_source g c
  · rw [hafter, hu, hv]
    simp [initialChunk, renderChunks, List.map_append, List.flatten_append]
    rfl

private lemma goodForm_step (g : grammar T) (hg : grammar_noncontracting g)
    {before after : List (symbol (Bool × T) (StarNT g.nt))}
    (hgood : GoodForm g before)
    (hstep : grammar_transforms (alternatingGrammar g) before after) :
    GoodForm g after := by
  rcases hstep with ⟨r, hr, u, v, hbefore, hafter⟩
  simp only [alternatingGrammar, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | ⟨r₀, hr₀, hrule⟩
  · apply goodForm_continue_step g false hgood
    · simpa [continueRule, generator, List.append_assoc] using hbefore
    · simpa [continueRule, generator, tagSym, List.append_assoc] using hafter
  · apply goodForm_stop_step g false hgood
    · simpa [stopRule, generator, List.append_assoc] using hbefore
    · simpa [stopRule, tagSym, List.append_assoc] using hafter
  · apply goodForm_continue_step g true hgood
    · simpa [continueRule, generator, List.append_assoc] using hbefore
    · simpa [continueRule, generator, tagSym, List.append_assoc] using hafter
  · apply goodForm_stop_step g true hgood
    · simpa [stopRule, generator, List.append_assoc] using hbefore
    · simpa [stopRule, tagSym, List.append_assoc] using hafter
  · rcases hrule with rfl | rfl
    · exact goodForm_tagRule_step g hg false hr₀ hgood hbefore hafter
    · exact goodForm_tagRule_step g hg true hr₀ hgood hbefore hafter

private lemma goodForm_derives (g : grammar T) (hg : grammar_noncontracting g)
    {sf : List (symbol (Bool × T) (StarNT g.nt))}
    (h : grammar_derives (alternatingGrammar g)
      [symbol.nonterminal (alternatingGrammar g).initial] sf) :
    GoodForm g sf := by
  induction h with
  | refl => exact goodForm_initial g
  | tail _ hs ih => exact goodForm_step g hg ih hs

/-! ## Reading a terminal good form -/

/-- Forget the colour of a symbol of the alternating grammar.  The generator case is
irrelevant below, but giving it an arbitrary nonterminal value makes this a total map. -/
private def untagSym (g : grammar T) :
    symbol (Bool × T) (StarNT g.nt) → symbol T g.nt
  | .terminal (_, a) => .terminal a
  | .nonterminal (.inl (_, N)) => .nonterminal N
  | .nonterminal (.inr _) => .nonterminal g.initial

@[simp]
private lemma untagSym_tagSym (g : grammar T) (c : Bool) (x : symbol T g.nt) :
    untagSym g (tagSym c x) = x := by
  cases x <;> rfl

@[simp]
private lemma untagSym_terminal (g : grammar T) (x : Bool × T) :
    untagSym g (.terminal x) = .terminal x.2 := by
  cases x
  rfl

private lemma untagSym_map_tagSym (g : grammar T) (c : Bool)
    (s : List (symbol T g.nt)) :
    (s.map (tagSym c)).map (untagSym g) = s := by
  induction s with
  | nil => rfl
  | cons x xs ih => simp [ih]

private lemma untagSym_map_terminal (g : grammar T) (w : List (Bool × T)) :
    (w.map symbol.terminal).map (untagSym g) =
      (w.map Prod.snd).map symbol.terminal := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨c, a⟩
      simp [ih]

private lemma terminal_chunks_factors (g : grammar T)
    {chunks : List (Bool × List (symbol (Bool × T) (StarNT g.nt)))}
    (hsources : ∀ ch ∈ chunks, SourceChunk g ch)
    {w : List (Bool × T)}
    (hform : w.map symbol.terminal = renderChunks chunks) :
    ∃ words : List (List T),
      w.map Prod.snd = words.flatten ∧
      ∀ word ∈ words, word ∈ grammar_language g := by
  induction chunks generalizing w with
  | nil =>
      simp only [renderChunks, List.map_nil, List.flatten_nil] at hform
      have hw : w = [] := List.map_eq_nil_iff.mp hform
      subst w
      exact ⟨[], by simp⟩
  | cons ch chunks ih =>
      have hsource : SourceChunk g ch := hsources ch (by simp)
      have hsources' : ∀ ch' ∈ chunks, SourceChunk g ch' := by
        intro ch' hch'
        exact hsources ch' (by simp [hch'])
      let n := ch.2.length
      let headWord := w.take n
      let tailWord := w.drop n
      have hheadWord : headWord.map symbol.terminal = ch.2 := by
        have := congrArg (List.take n) hform
        simpa [headWord, n, renderChunks, List.map_take] using this
      have htailWord : tailWord.map symbol.terminal = renderChunks chunks := by
        have := congrArg (List.drop n) hform
        simpa [tailWord, n, renderChunks, List.map_drop] using this
      obtain ⟨s, hs0, hderiv, hshape⟩ := hsource
      have htagged : s.map (tagSym ch.1) = headWord.map symbol.terminal :=
        hshape.symm.trans hheadWord.symm
      have hsourceWord : s = (headWord.map Prod.snd).map symbol.terminal := by
        have := congrArg (List.map (untagSym g)) htagged
        rw [untagSym_map_tagSym, untagSym_map_terminal] at this
        exact this
      have hheadLanguage : headWord.map Prod.snd ∈ grammar_language g := by
        change grammar_derives g [.nonterminal g.initial]
          ((headWord.map Prod.snd).map symbol.terminal)
        simpa [hsourceWord] using hderiv
      obtain ⟨words, hwordsEq, hwords⟩ := ih hsources' htailWord
      refine ⟨headWord.map Prod.snd :: words, ?_, ?_⟩
      · have hsplit : w = headWord ++ tailWord := by
          change w = w.take n ++ w.drop n
          exact (List.take_append_drop n w).symm
        rw [hsplit, List.map_append, hwordsEq]
        rfl
      · intro word hword
        simp only [List.mem_cons] at hword
        rcases hword with rfl | hword
        · exact hheadLanguage
        · exact hwords word hword

private lemma alternatingGrammar_sound (g : grammar T)
    (hg : grammar_noncontracting g) {w : List (Bool × T)}
    (hw : w ∈ grammar_language (alternatingGrammar g)) :
    w.map Prod.snd ∈ KStar.kstar (grammar_language g) := by
  have hgood := goodForm_derives g hg hw
  rcases hgood with ⟨chunks, _halt, hsources, hform⟩ |
      ⟨chunks, c, _halt, hsources, hform⟩
  · obtain ⟨words, hwordsEq, hwords⟩ :=
      terminal_chunks_factors g hsources hform
    rw [Language.mem_kstar]
    exact ⟨words, hwordsEq, hwords⟩
  · exfalso
    have hgenerator : (@generator T g.nt c) ∈
        w.map (@symbol.terminal (Bool × T) (StarNT g.nt)) := by
      rw [hform]
      simp [renderChunks, generatorChunk]
    simp [generator] at hgenerator

/-! ## Erasing the colours -/

private def forgetColour (x : Bool × T) : List T := [x.2]

private lemma forgetColour_epsfree : IsEpsFreeHomomorphism (@forgetColour T) := by
  intro x
  simp [forgetColour]

private lemma flatMap_forgetColour (w : List (Bool × T)) :
    w.flatMap forgetColour = w.map Prod.snd := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [forgetColour, ih]

private lemma taggedWords_forget (c : Bool) (words : List (List T)) :
    (taggedWords c words).flatMap forgetColour = words.flatten := by
  induction words generalizing c with
  | nil => rfl
  | cons word words ih =>
      have hword : (word.map (c, ·)).flatMap forgetColour = word := by
        induction word with
        | nil => rfl
        | cons a word ihword => simp [forgetColour, ihword]
      simp [taggedWords, hword, ih]

private lemma noncontracting_derives_length_le' (g : grammar T)
    (hg : grammar_noncontracting g)
    {x y : List (symbol T g.nt)} (h : grammar_derives g x y) :
    x.length ≤ y.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih =>
      exact le_trans ih (noncontracting_transforms_length_le g hg hstep)

private lemma alternating_image_eq_star_diff_empty (g : grammar T)
    (hg : grammar_noncontracting g) :
    (grammar_language (alternatingGrammar g)).homomorphicImage forgetColour =
      KStar.kstar (grammar_language g) \ ({[]} : Set (List T)) := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_homomorphicImage_iff_flatMap] at hw
    obtain ⟨coloured, hcoloured, rfl⟩ := hw
    constructor
    · rw [flatMap_forgetColour]
      exact alternatingGrammar_sound g hg hcoloured
    · intro hempty
      rw [Set.mem_singleton_iff] at hempty
      have hlen := noncontracting_derives_length_le'
        (alternatingGrammar g) (alternatingGrammar_noncontracting g hg) hcoloured
      cases coloured with
      | nil => simp at hlen
      | cons x xs => simp [forgetColour] at hempty
  · rintro ⟨hw, hw0⟩
    rw [Language.mem_kstar] at hw
    obtain ⟨words, rfl, hwords⟩ := hw
    have hwords0 : words ≠ [] := by
      intro hnil
      subst words
      exact hw0 (by simp)
    rw [Language.mem_homomorphicImage_iff_flatMap]
    refine ⟨taggedWords false words,
      alternatingGrammar_complete g hwords0 hwords, ?_⟩
    exact taggedWords_forget false words

/-! Removing `ε` from the base language does not change its Kleene star. -/

private lemma flatten_filter_ne_nil (words : List (List T)) :
    (words.filter fun word => word ≠ []).flatten = words.flatten := by
  classical
  induction words with
  | nil => rfl
  | cons word words ih =>
      by_cases hword : word = []
      · subst word
        simpa using ih
      · have hp : decide (word ≠ []) = true := by simp [hword]
        rw [List.filter_cons_of_pos
          (p := fun word : List T => decide (word ≠ [])) hp]
        change word ++ (words.filter fun word => word ≠ []).flatten =
          word ++ words.flatten
        rw [ih]

private lemma kstar_remove_empty (L : Language T) :
    KStar.kstar (L \ ({[]} : Set (List T))) = KStar.kstar L := by
  classical
  ext w
  constructor
  · intro hw
    rw [Language.mem_kstar] at hw ⊢
    obtain ⟨words, rfl, hwords⟩ := hw
    exact ⟨words, rfl, fun word hword => (hwords word hword).1⟩
  · intro hw
    rw [Language.mem_kstar] at hw ⊢
    obtain ⟨words, rfl, hwords⟩ := hw
    refine ⟨words.filter (fun word => word ≠ []),
      (flatten_filter_ne_nil words).symm, ?_⟩
    intro word hword
    simp only [List.mem_filter] at hword
    exact ⟨hwords word hword.1, by simpa [Set.mem_singleton_iff] using hword.2⟩

end ContextSensitiveStar

open ContextSensitiveStar

/-- Context-sensitive languages are closed under Kleene star. -/
public theorem CS_closedUnderKleeneStar :
    ClosedUnderKleeneStar (α := T) is_CS := by
  intro L hL
  obtain ⟨g, hg, hlang⟩ := hL
  obtain ⟨g₀, _hfinite, hnc, hlang₀⟩ :=
    exists_noncontracting_offEmpty_of_CS g hg
  have hcoloured : is_CS (grammar_language (alternatingGrammar g₀)) :=
    ⟨alternatingGrammar g₀,
      grammar_context_sensitive_of_noncontracting _
        (alternatingGrammar_noncontracting g₀ hnc), rfl⟩
  have himage : is_CS
      ((grammar_language (alternatingGrammar g₀)).homomorphicImage forgetColour) :=
    is_CS_homomorphicImage_epsfree _ _ forgetColour_epsfree hcoloured
  apply is_CS_of_diff_empty_of_is_CS
  have heq :
      (grammar_language (alternatingGrammar g₀)).homomorphicImage forgetColour =
        KStar.kstar L \ ({[]} : Set (List T)) := by
    rw [alternating_image_eq_star_diff_empty g₀ hnc, hlang₀, hlang,
      kstar_remove_empty]
  rwa [← heq]
