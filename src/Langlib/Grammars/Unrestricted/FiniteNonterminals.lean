import Langlib.Grammars.Unrestricted.Definition
import Langlib.Grammars.Unrestricted.Toolbox
import Mathlib

/-!
# Every unrestricted grammar is equivalent to one with finitely many nonterminals

Since an unrestricted `grammar` stores its rules in a `List`, only finitely many
nonterminals can ever appear in a derivation from the initial symbol. We restrict
the nonterminal type to those that actually occur in the grammar, producing an
equivalent grammar whose nonterminal type carries a `Fintype` instance.

## Main results

- `restrictGrammar` — restrict any grammar to one with `Fintype` nonterminals.
- `grammar_language_eq_restrictGrammar` — the restricted grammar generates the same language.
- `grammar_equivalent_finiteNT` — every unrestricted grammar has an equivalent one
  with `Finite` nonterminals.
-/

open Relation

noncomputable section

open scoped Classical

variable {T : Type}

/-! ## Extracting nonterminals from symbol lists -/

/-- Extract all nonterminals from a list of symbols. -/
def symbolsNTs {N : Type} : List (symbol T N) → List N
  | [] => []
  | symbol.terminal _ :: rest => symbolsNTs rest
  | symbol.nonterminal n :: rest => n :: symbolsNTs rest

@[simp] lemma symbolsNTs_nil {N : Type} : @symbolsNTs T N [] = [] := rfl

@[simp] lemma symbolsNTs_cons_terminal {N : Type} (t : T) (l : List (symbol T N)) :
    symbolsNTs (symbol.terminal t :: l) = symbolsNTs l := rfl

@[simp] lemma symbolsNTs_cons_nonterminal {N : Type} (n : N) (l : List (symbol T N)) :
    symbolsNTs (symbol.nonterminal n :: l) = n :: symbolsNTs l := rfl

lemma mem_symbolsNTs_iff {N : Type} {n : N} {l : List (symbol T N)} :
    n ∈ symbolsNTs l ↔ symbol.nonterminal n ∈ l := by
  induction' l with s l ih;
  · aesop;
  · cases s <;> aesop

lemma symbolsNTs_append {N : Type} (l₁ l₂ : List (symbol T N)) :
    symbolsNTs (l₁ ++ l₂) = symbolsNTs l₁ ++ symbolsNTs l₂ := by
  induction l₁ <;> simp +decide [ * ];
  cases ‹symbol T N› <;> simp +decide [ * ]

lemma symbolsNTs_map_terminal {N : Type} (w : List T) :
    symbolsNTs (w.map (symbol.terminal (N := N))) = [] := by
  induction w <;> aesop

/-! ## Used nonterminals of a grammar -/

/-- All nonterminals mentioned in a grammar rule. -/
def ruleNTs {N : Type} (r : grule T N) : List N :=
  symbolsNTs r.input_L ++ [r.input_N] ++ symbolsNTs r.input_R ++ symbolsNTs r.output_string

/-- The list of all nonterminals used in a grammar. -/
def usedNTsList (g : grammar T) : List g.nt :=
  [g.initial] ++ g.rules.flatMap ruleNTs

/-- The finite set of all nonterminals used in a grammar. -/
def usedNTs (g : grammar T) : Finset g.nt :=
  (usedNTsList g).toFinset

lemma initial_mem_usedNTs (g : grammar T) : g.initial ∈ usedNTs g := by
  unfold usedNTs;
  simp [usedNTsList]

lemma ruleNT_mem_usedNTs {g : grammar T} {r : grule T g.nt} {n : g.nt}
    (hr : r ∈ g.rules) (hn : n ∈ ruleNTs r) : n ∈ usedNTs g := by
  exact List.mem_toFinset.mpr ( List.mem_append.mpr ( Or.inr ( List.mem_flatMap.mpr ⟨ r, hr, hn ⟩ ) ) )

lemma inputN_mem_ruleNTs {N : Type} (r : grule T N) : r.input_N ∈ ruleNTs r := by
  unfold ruleNTs; simp +decide ;

/-! ## The restricted grammar -/

/-- The subtype of used nonterminals. -/
abbrev UsedNT (g : grammar T) := { n : g.nt // n ∈ usedNTs g }

instance usedNT_fintype (g : grammar T) : Fintype (UsedNT g) :=
  Fintype.subtype (usedNTs g) (fun _ => Iff.rfl)

/-- Restrict a nonterminal to `UsedNT g`. Maps unused nonterminals to the initial symbol. -/
def restrictNT (g : grammar T) (n : g.nt) : UsedNT g :=
  if h : n ∈ usedNTs g then ⟨n, h⟩ else ⟨g.initial, initial_mem_usedNTs g⟩

/-- Restrict a symbol to `UsedNT g`. -/
def restrictSym (g : grammar T) : symbol T g.nt → symbol T (UsedNT g)
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal n => symbol.nonterminal (restrictNT g n)

/-- Embed a symbol over `UsedNT g` back into a symbol over `g.nt`. -/
def embedSym (g : grammar T) : symbol T (UsedNT g) → symbol T g.nt
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal ⟨n, _⟩ => symbol.nonterminal n

/-- The grammar restricted to its used nonterminals. -/
def restrictGrammar (g : grammar T) : grammar T where
  nt := UsedNT g
  initial := ⟨g.initial, initial_mem_usedNTs g⟩
  rules := g.rules.map (fun r =>
    { input_L := r.input_L.map (restrictSym g)
      input_N := restrictNT g r.input_N
      input_R := r.input_R.map (restrictSym g)
      output_string := r.output_string.map (restrictSym g) })

instance restrictGrammar_fintype (g : grammar T) : Fintype (restrictGrammar g).nt :=
  usedNT_fintype g

/-! ## Properties of `restrictSym` and `embedSym` -/

lemma restrictNT_of_mem {g : grammar T} {n : g.nt} (h : n ∈ usedNTs g) :
    restrictNT g n = ⟨n, h⟩ := by
  exact dif_pos h

@[simp] lemma restrictSym_terminal (g : grammar T) (t : T) :
    restrictSym g (symbol.terminal t : symbol T g.nt) = symbol.terminal t := rfl

@[simp] lemma embedSym_terminal (g : grammar T) (t : T) :
    embedSym g (symbol.terminal t : symbol T (UsedNT g)) = symbol.terminal t := rfl

lemma restrictSym_embedSym (g : grammar T) (s : symbol T (UsedNT g)) :
    restrictSym g (embedSym g s) = s := by
  -- Let's split into cases based on `s`. If `s` is a terminal, both functions return it as is. If `s` is a nonterminal, applying `embedSym` and then `restrictSym` brings it back to the original nonterminal.
  cases s <;> simp [restrictSym, embedSym];
  rename_i n;
  convert restrictNT_of_mem n.2

lemma embedSym_restrictSym {g : grammar T} {s : symbol T g.nt}
    (h : ∀ n, s = symbol.nonterminal n → n ∈ usedNTs g) :
    embedSym g (restrictSym g s) = s := by
  unfold restrictSym embedSym restrictNT; aesop;

/-! ## The `allNTsUsed` predicate -/

/-- All nonterminals in a symbol list belong to `usedNTs g`. -/
def allNTsUsed (g : grammar T) (l : List (symbol T g.nt)) : Prop :=
  ∀ n, symbol.nonterminal n ∈ l → n ∈ usedNTs g

lemma allNTsUsed_nil (g : grammar T) : allNTsUsed g [] := by
  intro n hn; exact absurd hn (List.not_mem_nil)

lemma allNTsUsed_append {g : grammar T} {l₁ l₂ : List (symbol T g.nt)} :
    allNTsUsed g (l₁ ++ l₂) ↔ allNTsUsed g l₁ ∧ allNTsUsed g l₂ := by
  unfold allNTsUsed; aesop;

lemma allNTsUsed_singleton_nonterminal {g : grammar T} {n : g.nt} :
    allNTsUsed g [symbol.nonterminal n] ↔ n ∈ usedNTs g := by
  unfold allNTsUsed; aesop;

lemma allNTsUsed_initial (g : grammar T) :
    allNTsUsed g [symbol.nonterminal g.initial] := by
  convert initial_mem_usedNTs g using 1;
  exact?

lemma allNTsUsed_of_rule_input_L {g : grammar T} {r : grule T g.nt} (hr : r ∈ g.rules) :
    allNTsUsed g r.input_L := by
  intro n hn
  apply ruleNT_mem_usedNTs hr
  simp [ruleNTs];
  exact Or.inl <| by simpa using mem_symbolsNTs_iff.mpr hn;

lemma allNTsUsed_of_rule_input_R {g : grammar T} {r : grule T g.nt} (hr : r ∈ g.rules) :
    allNTsUsed g r.input_R := by
  intro n hn;
  apply ruleNT_mem_usedNTs hr;
  unfold ruleNTs; simp_all +decide [ mem_symbolsNTs_iff ] ;

lemma allNTsUsed_of_rule_output {g : grammar T} {r : grule T g.nt} (hr : r ∈ g.rules) :
    allNTsUsed g r.output_string := by
  intro n hn;
  apply ruleNT_mem_usedNTs hr;
  exact List.mem_append_right _ ( by simpa using List.mem_toFinset.mp ( List.mem_toFinset.mpr <| by simpa using mem_symbolsNTs_iff.mpr hn ) )

/-! ## Roundtrip properties for lists -/

lemma map_embedSym_map_restrictSym {g : grammar T} {l : List (symbol T g.nt)}
    (h : allNTsUsed g l) :
    (l.map (restrictSym g)).map (embedSym g) = l := by
  refine' List.ext_get _ _ <;> simp_all +decide;
  intro n hn; cases h' : l[n] <;> simp_all +decide [ embedSym, restrictSym ] ;
  have := h _ ( h' ▸ List.getElem_mem _ ) ; unfold restrictNT; aesop;

lemma map_restrictSym_map_embedSym (g : grammar T) (l : List (symbol T (UsedNT g))) :
    (l.map (embedSym g)).map (restrictSym g) = l := by
  exact List.ext_get ( by simp +decide ) ( by simp +decide [ Function.comp, restrictSym_embedSym ] )

lemma map_restrictSym_terminal (g : grammar T) (w : List T) :
    (w.map (fun t => symbol.terminal (N := g.nt) t)).map (restrictSym g) =
    w.map (fun t => symbol.terminal (N := UsedNT g) t) := by
  induction w <;> simp_all +decide [ restrictSym ]

lemma map_embedSym_terminal (g : grammar T) (w : List T) :
    (w.map (fun t => symbol.terminal (N := UsedNT g) t)).map (embedSym g) =
    w.map (fun t => symbol.terminal (N := g.nt) t) := by
  induction w <;> aesop

/-! ## Preservation of `allNTsUsed` through derivations -/

lemma allNTsUsed_preserved_by_transform {g : grammar T} {u v : List (symbol T g.nt)}
    (ht : grammar_transforms g u v) (hu : allNTsUsed g u) : allNTsUsed g v := by
  obtain ⟨r, hr, u_prefix, v_suffix, hu_eq, hv_eq⟩ := ht;
  simp_all +decide [ allNTsUsed_append ];
  simp_all +decide [ allNTsUsed ];
  exact fun n hn => by have := allNTsUsed_of_rule_output hr; exact this n hn;

lemma allNTsUsed_preserved_by_derives {g : grammar T} {u v : List (symbol T g.nt)}
    (hd : grammar_derives g u v) (hu : allNTsUsed g u) : allNTsUsed g v := by
  induction hd;
  · assumption;
  · exact?

/-! ## Rule membership in the restricted grammar -/

lemma restrictGrammar_rule_of_mem {g : grammar T} {r : grule T g.nt} (hr : r ∈ g.rules) :
    (grule.mk (r.input_L.map (restrictSym g)) (restrictNT g r.input_N)
      (r.input_R.map (restrictSym g)) (r.output_string.map (restrictSym g)))
    ∈ (restrictGrammar g).rules := by
  exact List.mem_map.mpr ⟨ r, hr, rfl ⟩

lemma restrictGrammar_rule_mem {g : grammar T} {r' : grule T (UsedNT g)}
    (hr' : r' ∈ (restrictGrammar g).rules) :
    ∃ r ∈ g.rules,
      r'.input_L = r.input_L.map (restrictSym g) ∧
      r'.input_N = restrictNT g r.input_N ∧
      r'.input_R = r.input_R.map (restrictSym g) ∧
      r'.output_string = r.output_string.map (restrictSym g) := by
  unfold restrictGrammar at hr';
  grind

/-! ## Derivation correspondence -/

/-
Forward direction: a transform in `g` lifts to `restrictGrammar g` when all
    nonterminals in the source are used.
-/
lemma transforms_restrict {g : grammar T} {u v : List (symbol T g.nt)}
    (ht : grammar_transforms g u v) (hu : allNTsUsed g u) :
    grammar_transforms (restrictGrammar g)
      (u.map (restrictSym g)) (v.map (restrictSym g)) := by
  obtain ⟨ r, hr, u_prefix, v_suffix, hu_eq, hv_eq ⟩ := ht;
  refine' ⟨ _, restrictGrammar_rule_of_mem hr, List.map ( restrictSym g ) u_prefix, List.map ( restrictSym g ) v_suffix, _, _ ⟩ <;> simp +decide [ *, List.map_append ];
  exact?

/-
Forward direction lifted to multi-step derivation.
-/
lemma derives_restrict {g : grammar T} {u v : List (symbol T g.nt)}
    (hd : grammar_derives g u v) (hu : allNTsUsed g u) :
    grammar_derives (restrictGrammar g)
      (u.map (restrictSym g)) (v.map (restrictSym g)) := by
  induction' hd with u v hd ih;
  · constructor;
  · apply_rules [ Relation.ReflTransGen.tail, transforms_restrict ];
    exact?

/-
Backward direction: a transform in `restrictGrammar g` embeds into `g`.
-/
lemma transforms_embed {g : grammar T} {u v : List (symbol T (UsedNT g))}
    (ht : grammar_transforms (restrictGrammar g) u v) :
    grammar_transforms g (u.map (embedSym g)) (v.map (embedSym g)) := by
  obtain ⟨ r', hr', u', v', rfl, rfl ⟩ := ht;
  obtain ⟨ r, hr, hr' ⟩ := restrictGrammar_rule_mem hr';
  refine' ⟨ r, hr, List.map ( embedSym g ) u', List.map ( embedSym g ) v', _, _ ⟩ <;> simp +decide [ *, List.map_append ];
  · congr! 2;
    · convert map_embedSym_map_restrictSym ( allNTsUsed_of_rule_input_L hr ) using 1;
      rw [ List.map_map ];
    · rw [ restrictNT_of_mem ( ruleNT_mem_usedNTs hr ( inputN_mem_ruleNTs r ) ) ];
      rfl;
    · congr! 1;
      convert map_embedSym_map_restrictSym ( allNTsUsed_of_rule_input_R hr ) using 1;
      rw [ List.map_map ];
  · convert map_embedSym_map_restrictSym ( allNTsUsed_of_rule_output hr ) using 1;
    rw [ List.map_map ]

/-
Backward direction lifted to multi-step derivation.
-/
lemma derives_embed {g : grammar T} {u v : List (symbol T (UsedNT g))}
    (hd : grammar_derives (restrictGrammar g) u v) :
    grammar_derives g (u.map (embedSym g)) (v.map (embedSym g)) := by
  -- We'll use induction on `hd` to show that the derivation in the restricted grammar implies a derivation in the original grammar.
  induction' hd with u v huv ih;
  · constructor;
  · exact grammar_deri_of_deri_tran ‹_› ( transforms_embed ih )

/-! ## Main theorem -/

/-
The restricted grammar generates exactly the same language as the original.
-/
theorem grammar_language_eq_restrictGrammar (g : grammar T) :
    grammar_language g = grammar_language (restrictGrammar g) := by
  unfold grammar_language;
  ext w;
  constructor;
  · intro hw;
    convert derives_restrict hw ( allNTsUsed_initial g ) using 1;
    simp +decide;
    simp +decide [restrictSym];
    simp +decide [setOf, restrictNT_of_mem (initial_mem_usedNTs g)];
    rfl;
  · intro hw;
    convert derives_embed hw using 1;
    unfold grammar_generates; aesop;

/-- Every unrestricted grammar is equivalent to one with finitely many nonterminals. -/
theorem grammar_equivalent_finiteNT (g : grammar T) :
    ∃ (g' : grammar T), Finite g'.nt ∧ grammar_language g = grammar_language g' :=
  ⟨restrictGrammar g, Finite.of_fintype _, grammar_language_eq_restrictGrammar g⟩

end