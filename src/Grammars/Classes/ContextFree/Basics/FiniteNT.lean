import Mathlib

/-!
# Every context-free grammar has an equivalent one with finite nonterminals

Since a `ContextFreeGrammar` stores its rules in a `Finset`, only finitely many
nonterminals can ever appear in a derivation. We restrict the nonterminal type to
those that actually occur in the grammar, producing an equivalent grammar whose
nonterminal type is `Fintype`.

## Main results

- `ContextFreeGrammar.toFiniteNT` — restrict any CFG to one with `Fintype NT`.
- `ContextFreeGrammar.toFiniteNT_language` — the restricted grammar generates the same language.
- `ContextFreeGrammar.exists_fintype_nt` — every context-free language has a grammar
  with `Fintype NT`.
-/

open Symbol

noncomputable section

open scoped Classical

namespace ContextFreeGrammar

variable {T : Type}

/-! ## Used nonterminals -/

/-- The finite set of nonterminals occurring in the grammar (rules + start symbol). -/
noncomputable def usedNT (g : ContextFreeGrammar T) : Finset g.NT :=
  {g.initial} ∪
    g.rules.biUnion (fun r =>
      {r.input} ∪ (r.output.filterMap (fun s =>
        match s with | .nonterminal n => some n | .terminal _ => none)).toFinset)

theorem initial_mem_usedNT (g : ContextFreeGrammar T) : g.initial ∈ g.usedNT := by
  unfold usedNT; simp

theorem input_mem_usedNT (g : ContextFreeGrammar T) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) : r.input ∈ g.usedNT := by
  unfold usedNT
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
  right; exact ⟨r, hr, by simp⟩

theorem output_nonterminal_mem_usedNT (g : ContextFreeGrammar T) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) {n : g.NT} (hn : Symbol.nonterminal n ∈ r.output) :
    n ∈ g.usedNT := by
  unfold usedNT
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
  right
  refine ⟨r, hr, ?_⟩
  right
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨.nonterminal n, hn, rfl⟩

/-- The restricted nonterminal type: nonterminals actually appearing in the grammar. -/
def UsedNT (g : ContextFreeGrammar T) := { n : g.NT // n ∈ g.usedNT }

noncomputable instance instFintypeUsedNT (g : ContextFreeGrammar T) : Fintype g.UsedNT :=
  Fintype.subtype g.usedNT (fun _ => Iff.rfl)

/-! ## Symbol embedding and restriction -/

/-- Embed a symbol over the restricted nonterminals back to the original type. -/
def liftSymbol (g : ContextFreeGrammar T) : Symbol T g.UsedNT → Symbol T g.NT
  | .terminal t => .terminal t
  | .nonterminal ⟨n, _⟩ => .nonterminal n

/-- Embed a word over restricted nonterminals back to the original type. -/
def liftWord (g : ContextFreeGrammar T) : List (Symbol T g.UsedNT) → List (Symbol T g.NT) :=
  List.map g.liftSymbol

/-
PROVIDED SOLUTION
Case split on both symbols. For terminals, injectivity is immediate. For nonterminals, use Subtype.ext.
-/
theorem liftSymbol_injective (g : ContextFreeGrammar T) : Function.Injective g.liftSymbol := by
  intro a b; unfold ContextFreeGrammar.liftSymbol; aesop;

theorem liftWord_append (g : ContextFreeGrammar T) (u v : List (Symbol T g.UsedNT)) :
    g.liftWord (u ++ v) = g.liftWord u ++ g.liftWord v := by
  simp [liftWord]

/-
PROVIDED SOLUTION
Unfold liftWord as List.map, then use List.map_map and show liftSymbol ∘ terminal = terminal.
-/
theorem liftWord_map_terminal (g : ContextFreeGrammar T) (w : List T) :
    g.liftWord (w.map .terminal) = w.map .terminal := by
  unfold ContextFreeGrammar.liftWord; aesop;

/-- Restrict a single symbol, given that any nonterminal in it is used. -/
def restrictOneSymbol (g : ContextFreeGrammar T)
    (s : Symbol T g.NT) (h : ∀ n, s = .nonterminal n → n ∈ g.usedNT) :
    Symbol T g.UsedNT :=
  match s, h with
  | .terminal t, _ => .terminal t
  | .nonterminal n, h => .nonterminal ⟨n, h n rfl⟩

/-
PROVIDED SOLUTION
Case split on s. Both cases are definitional.
-/
theorem liftSymbol_restrictOneSymbol (g : ContextFreeGrammar T)
    (s : Symbol T g.NT) (h : ∀ n, s = .nonterminal n → n ∈ g.usedNT) :
    g.liftSymbol (g.restrictOneSymbol s h) = s := by
  cases s <;> aesop

/-! ## All-used predicate -/

/-- All nonterminals in a word are used. -/
def AllUsed (g : ContextFreeGrammar T) (w : List (Symbol T g.NT)) : Prop :=
  ∀ s ∈ w, ∀ n, s = Symbol.nonterminal n → n ∈ g.usedNT

/-
PROVIDED SOLUTION
The only symbol is nonterminal g.initial, and g.initial ∈ g.usedNT by initial_mem_usedNT.
-/
theorem allUsed_initial (g : ContextFreeGrammar T) :
    g.AllUsed [Symbol.nonterminal g.initial] := by
  -- Since the only symbol in the word is nonterminal g.initial, and g.initial is in the usedNT set by definition, the AllUsed predicate holds.
  simp [AllUsed, initial_mem_usedNT]

/-
PROVIDED SOLUTION
Unfold AllUsed, use List.mem_append and split.
-/
theorem allUsed_append (g : ContextFreeGrammar T) {u v : List (Symbol T g.NT)} :
    g.AllUsed (u ++ v) ↔ g.AllUsed u ∧ g.AllUsed v := by
  unfold ContextFreeGrammar.AllUsed; aesop;

/-
PROVIDED SOLUTION
Unfold AllUsed, use List.mem_cons and split.
-/
theorem allUsed_cons (g : ContextFreeGrammar T) {s : Symbol T g.NT}
    {w : List (Symbol T g.NT)} :
    g.AllUsed (s :: w) ↔ (∀ n, s = .nonterminal n → n ∈ g.usedNT) ∧ g.AllUsed w := by
  unfold ContextFreeGrammar.AllUsed; aesop;

/-
PROVIDED SOLUTION
Use output_nonterminal_mem_usedNT for each nonterminal in the output.
-/
theorem allUsed_output (g : ContextFreeGrammar T) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) : g.AllUsed r.output := by
  -- Apply the hypothesis `h_output` to each element in the output list.
  intros s hs n hn
  apply output_nonterminal_mem_usedNT g hr (by
  aesop)

/-
PROVIDED SOLUTION
Decompose the Produces into a rule application: u = p ++ [nonterminal r.input] ++ q, v = p ++ r.output ++ q. Use allUsed_append to split hu, then rebuild with allUsed_output for r.output.
-/
theorem allUsed_produces (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} (h : g.Produces u v) (hu : g.AllUsed u) :
    g.AllUsed v := by
  induction h;
  rename_i r hr;
  obtain ⟨ p, q, hp, hq ⟩ := hr.2.exists_parts;
  simp_all +decide [ allUsed_append, allUsed_cons ];
  exact allUsed_output g hr.1

/-
PROVIDED SOLUTION
Induction on the derivation. Base case is trivial. Inductive step uses allUsed_produces.
-/
theorem allUsed_derives (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v) (hu : g.AllUsed u) :
    g.AllUsed v := by
  contrapose h;
  intro hv
  induction' hv with u v huv ih;
  · contradiction;
  · exact h ( allUsed_produces g ih ( by tauto ) )

/-
PROVIDED SOLUTION
Every symbol in w.map terminal is a terminal, so the nonterminal condition is vacuously true.
-/
theorem allUsed_map_terminal (g : ContextFreeGrammar T) (w : List T) :
    g.AllUsed (w.map .terminal) := by
  intro s hs; aesop;

/-! ## Word restriction -/

/-- Restrict a word with all-used nonterminals to the restricted type. -/
def restrictWord (g : ContextFreeGrammar T) (w : List (Symbol T g.NT)) (hw : g.AllUsed w) :
    List (Symbol T g.UsedNT) :=
  w.pmap (fun s hs => g.restrictOneSymbol s (fun n hn => hw s hs n hn))
    (fun _ h => h)

/-
PROVIDED SOLUTION
Unfold liftWord and restrictWord. This is List.map liftSymbol (List.pmap ...). Use List.map_pmap to combine, then show each element maps back via liftSymbol_restrictOneSymbol. The result equals List.pmap (fun s _ => s) w ... which is w.
-/
theorem liftWord_restrictWord (g : ContextFreeGrammar T) (w : List (Symbol T g.NT))
    (hw : g.AllUsed w) : g.liftWord (g.restrictWord w hw) = w := by
  unfold ContextFreeGrammar.liftWord ContextFreeGrammar.restrictWord;
  grind +suggestions

/-
PROVIDED SOLUTION
Unfold restrictWord as List.pmap. Use List.pmap_append to split. The membership proofs match because allUsed_append splits.
-/
theorem restrictWord_append (g : ContextFreeGrammar T)
    (u v : List (Symbol T g.NT)) (hu : g.AllUsed u) (hv : g.AllUsed v)
    (huv : g.AllUsed (u ++ v)) :
    g.restrictWord (u ++ v) huv = g.restrictWord u hu ++ g.restrictWord v hv := by
  unfold restrictWord; simp +decide [ List.mem_append ] ;
  congr! 1;
  · exact?;
  · exact?

/-
PROVIDED SOLUTION
Unfold restrictWord and restrictOneSymbol. The pmap of a singleton list is a singleton. The result follows by definition.
-/
theorem restrictWord_initial (g : ContextFreeGrammar T) :
    g.restrictWord [.nonterminal g.initial] g.allUsed_initial =
    [.nonterminal ⟨g.initial, g.initial_mem_usedNT⟩] := by
  unfold restrictWord; aesop;

/-
PROVIDED SOLUTION
Induction on w. Base case: both sides are []. Step case: unfold pmap, the head maps to terminal t, and the tail follows by induction.
-/
theorem restrictWord_map_terminal (g : ContextFreeGrammar T) (w : List T)
    (hw : g.AllUsed (w.map .terminal)) :
    g.restrictWord (w.map .terminal) hw = w.map .terminal := by
  unfold ContextFreeGrammar.restrictWord;
  refine' List.ext_get _ _ <;> aesop

/-! ## The restricted grammar -/

/-- Restrict a rule to used nonterminals. -/
def restrictRule (g : ContextFreeGrammar T) (r : ContextFreeRule T g.NT)
    (hr : r ∈ g.rules) : ContextFreeRule T g.UsedNT where
  input := ⟨r.input, g.input_mem_usedNT hr⟩
  output := g.restrictWord r.output (g.allUsed_output hr)

theorem liftWord_restrictRule_output (g : ContextFreeGrammar T) (r : ContextFreeRule T g.NT)
    (hr : r ∈ g.rules) :
    g.liftWord (g.restrictRule r hr).output = r.output :=
  g.liftWord_restrictWord r.output (g.allUsed_output hr)

/-- The context-free grammar with nonterminals restricted to the finite used set. -/
noncomputable def toFiniteNT (g : ContextFreeGrammar T) : ContextFreeGrammar T where
  NT := g.UsedNT
  initial := ⟨g.initial, g.initial_mem_usedNT⟩
  rules := g.rules.attach.image (fun ⟨r, hr⟩ => g.restrictRule r hr)

noncomputable instance toFiniteNT_fintype (g : ContextFreeGrammar T) :
    Fintype g.toFiniteNT.NT := by
  unfold toFiniteNT
  exact instFintypeUsedNT g

theorem restrictRule_mem_toFiniteNT (g : ContextFreeGrammar T) (r : ContextFreeRule T g.NT)
    (hr : r ∈ g.rules) : g.restrictRule r hr ∈ g.toFiniteNT.rules :=
  Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_attach _ _, rfl⟩

/-
PROVIDED SOLUTION
Unfold toFiniteNT, use Finset.mem_image to extract the original rule from the attach.image.
-/
theorem mem_toFiniteNT_rules (g : ContextFreeGrammar T)
    (r' : ContextFreeRule T g.UsedNT) (hr' : r' ∈ g.toFiniteNT.rules) :
    ∃ (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules), r' = g.restrictRule r hr := by
  unfold ContextFreeGrammar.toFiniteNT at hr'; aesop;

/-! ## Direction 1: toFiniteNT derives → original derives -/

/-
PROVIDED SOLUTION
Extract the rule r' from h, use mem_toFiniteNT_rules to get the original rule r, use ContextFreeRule.Rewrites.exists_parts to get p, q. The original rule r has r.input = r'.input.val and liftWord r'.output = r.output (by liftWord_restrictRule_output). Construct the rewrite in g using liftWord_append and ContextFreeRule.rewrites_of_exists_parts.
-/
theorem liftWord_produces (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.UsedNT)}
    (h : g.toFiniteNT.Produces u v) :
    g.Produces (g.liftWord u) (g.liftWord v) := by
  -- Extract the rule r' from h, use mem_toFiniteNT_rules to get the original rule r, use ContextFreeRule.Rewrites.exists_parts to get p, q.
  obtain ⟨r', hr', hr''⟩ := h;
  obtain ⟨r, hr, hr'⟩ := mem_toFiniteNT_rules g r' hr';
  -- Use the parts p and q from the restricted rule's rewrites to construct the derivation in the original grammar.
  obtain ⟨p, q, hpq⟩ := hr''.exists_parts;
  -- Use the parts p and q to construct the derivation in the original grammar.
  have h_deriv : g.Produces (g.liftWord p ++ [Symbol.nonterminal r.input] ++ g.liftWord q) (g.liftWord p ++ r.output ++ g.liftWord q) := by
    constructor;
    exact ⟨ hr, ContextFreeRule.rewrites_of_exists_parts r ( g.liftWord p ) ( g.liftWord q ) ⟩;
  convert h_deriv using 1;
  · unfold ContextFreeGrammar.liftWord; aesop;
  · rw [ hpq.2, liftWord_append, liftWord_append ];
    rw [ hr', liftWord_restrictRule_output ]

/-
PROVIDED SOLUTION
Induction on the derivation. Base case is refl. Step uses liftWord_produces.
-/
theorem liftWord_derives (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.UsedNT)}
    (h : g.toFiniteNT.Derives u v) :
    g.Derives (g.liftWord u) (g.liftWord v) := by
  induction h;
  · constructor;
  · exact .trans ‹_› ( .single <| by exact? )

/-! ## Direction 2: original derives from initial → toFiniteNT derives -/

/-
PROVIDED SOLUTION
Extract the rule r from h. Get p, q from ContextFreeRule.Rewrites.exists_parts. The restricted rule restrictRule g r hr is in toFiniteNT.rules. We need to show restrictWord v hv = restrictWord (p ++ r.output ++ q) hv and restrictWord u hu = restrictWord (p ++ [nonterminal r.input] ++ q) hu, then use restrictWord_append to split, and construct the rewrite with ContextFreeRule.rewrites_of_exists_parts. The key is showing that restrictWord [nonterminal r.input] ... = [nonterminal ⟨r.input, ...⟩] and restrictWord r.output ... = (restrictRule g r hr).output.
-/
theorem restrictWord_produces (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} (h : g.Produces u v)
    (hu : g.AllUsed u) (hv : g.AllUsed v) :
    g.toFiniteNT.Produces (g.restrictWord u hu) (g.restrictWord v hv) := by
  obtain ⟨ r, hr, h ⟩ := h;
  refine' ⟨ g.restrictRule r hr, _, _ ⟩;
  · grind +suggestions;
  · obtain ⟨ p, q, hpq ⟩ := h.exists_parts;
    -- By definition of `restrictWord`, we can split the restriction into the restriction of `p`, the restriction of `[nonterminal r.input]`, and the restriction of `q`.
    have h_restrict_split : g.restrictWord u hu = g.restrictWord p (by
    intro s hs; specialize hu s; aesop;) ++ g.restrictWord [Symbol.nonterminal r.input] (by
    intro s hs n hn; aesop;) ++ g.restrictWord q (by
    intro s hs n hn; specialize hu s; aesop;) ∧ g.restrictWord v hv = g.restrictWord p (by
    intro s hs; specialize hu s; aesop;) ++ g.restrictWord r.output (by
    exact g.allUsed_output hr) ++ g.restrictWord q (by
    intro s hs n hn; specialize hu s; aesop;) := by
      grind +suggestions
    generalize_proofs at *;
    rw [ h_restrict_split.1, h_restrict_split.2 ];
    refine' ContextFreeRule.rewrites_of_exists_parts _ _ _

/-
PROVIDED SOLUTION
Induction on the derivation h. Base case: h is refl, so u = v, hence hu = hv gives refl. Step: have intermediate word b with g.Derives u b and g.Produces b v. By allUsed_derives, b is allUsed. Apply IH to get toFiniteNT.Derives, then restrictWord_produces for the last step.
-/
theorem restrictWord_derives (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v)
    (hu : g.AllUsed u) (hv : g.AllUsed v) :
    g.toFiniteNT.Derives (g.restrictWord u hu) (g.restrictWord v hv) := by
  induction' h with u v h ih;
  · grind;
  · rename_i h';
    convert Relation.ReflTransGen.tail ( h' ( show g.AllUsed u from ?_ ) ) ( restrictWord_produces g ih ( show g.AllUsed u from ?_ ) ( show g.AllUsed v from hv ) ) using 1;
    · exact?;
    · exact?

/-! ## Main theorem -/

/-
PROVIDED SOLUTION
Extensionality on words w. Forward: w ∈ toFiniteNT.language means toFiniteNT derives [nonterminal initial'] to w.map terminal. By liftWord_derives, g derives liftWord [nonterminal initial'] to liftWord (w.map terminal). The former is [nonterminal g.initial] and the latter is w.map terminal (by liftWord_map_terminal). So w ∈ g.language. Backward: w ∈ g.language means g derives [nonterminal g.initial] to w.map terminal. By allUsed_initial and allUsed_derives, w.map terminal is allUsed. By restrictWord_derives, toFiniteNT derives restrictWord [nonterminal g.initial] to restrictWord (w.map terminal). The former is [nonterminal initial'] (by restrictWord_initial) and the latter is w.map terminal (by restrictWord_map_terminal). So w ∈ toFiniteNT.language.
-/
theorem toFiniteNT_language (g : ContextFreeGrammar T) :
    g.toFiniteNT.language = g.language := by
  apply Set.ext;
  intro w
  constructor;
  · intro hw;
    convert liftWord_derives _ hw using 1;
    convert Iff.rfl using 3 ; unfold liftWord ; aesop;
  · intro hw
    obtain ⟨h_deriv, h_allUsed⟩ : g.Derives [Symbol.nonterminal g.initial] (w.map .terminal) ∧ g.AllUsed [Symbol.nonterminal g.initial] ∧ g.AllUsed (w.map .terminal) := by
      exact ⟨ hw, allUsed_initial g, allUsed_map_terminal g w ⟩;
    have h_restrict_deriv : g.toFiniteNT.Derives [Symbol.nonterminal ⟨g.initial, g.initial_mem_usedNT⟩] (g.restrictWord (w.map .terminal) h_allUsed.2) := by
      convert restrictWord_derives g h_deriv h_allUsed.1 h_allUsed.2 using 1;
    convert h_restrict_deriv.trans _;
    rw [ restrictWord_map_terminal ]

/-
PROVIDED SOLUTION
Obtain g from hL. Use toFiniteNT g, which has Fintype NT (toFiniteNT_fintype). Its language equals g.language by toFiniteNT_language, which equals L by hypothesis.
-/
theorem exists_fintype_nt (L : Language T) (hL : L.IsContextFree) :
    ∃ (g : ContextFreeGrammar T) (_ : Fintype g.NT), g.language = L := by
  obtain ⟨ g, hg ⟩ := hL;
  use g.toFiniteNT;
  exact ⟨ inferInstance, hg ▸ toFiniteNT_language g ⟩

end ContextFreeGrammar

end