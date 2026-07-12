module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Moves

@[expose]
public section

/-!
# Parse-directed scheduler execution

Ordinary parse execution and the unbounded semantic completeness theorem.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Ordinary parse-directed execution -/

/-- Focus the first symbol of a nonempty continuation word.  The empty fallback is convenient
for total statements; every use in the live runner is proved nonempty by its layout. -/
public def wordConfig (g : IndexedGrammar T) (inputPos : ℕ)
    (alpha word : List (WorkSym g)) : Config g :=
  match word with
  | [] => ⟨inputPos, ⟨alpha ++ [.dollar], .hash, []⟩⟩
  | z :: zs => ⟨inputPos, ⟨alpha ++ [.dollar], z, zs⟩⟩

/-- Productive moves leave an already stable frame prefix unchanged.  Initial and freshly
opened pop frames are stable. -/
public def StablePrefix {g : IndexedGrammar T} (alpha : List (WorkSym g)) : Prop :=
  markProductivePrefix alpha = alpha

@[simp] public theorem stablePrefix_nil (g : IndexedGrammar T) :
    StablePrefix (g := g) [] := by
  simp [StablePrefix]

public theorem stablePrefix_append_usedIndex {g : IndexedGrammar T}
    (alpha : List (WorkSym g)) (R : CFlag g) (d : IndexMark) :
    StablePrefix (alpha ++ [WorkSym.index R d.markUsed]) := by
  simp [StablePrefix]

public theorem SingletonLayout.input_ne_nil {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) (hne : flags ≠ []) : word ≠ [] := by
  intro hnil
  cases layout <;> simp_all

public theorem SingletonLayout.output_ne_nil {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) (hne : flags ≠ []) : used ≠ [] := by
  intro hnil
  cases layout <;> simp_all

/-! ### Stable-context constructors for the elementary moves -/

public theorem composite_plainBinary_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha beta : List (WorkSym g))
    (hstable : StablePrefix alpha) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, .plain C :: beta⟩⟩ := by
  refine ⟨.plainBinary A B C, hbinary, alpha, beta, rfl, ?_⟩
  change markProductivePrefix alpha = alpha at hstable
  simp [hstable]

public theorem composite_plainTerminal_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A : g.nt} {a : T} (hterminal : AugTerminal g A a)
    (inputPos : ℕ) (alpha beta : List (WorkSym g))
    (hstable : StablePrefix alpha) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .terminal a, beta⟩⟩ := by
  refine ⟨.plainTerminal A a, hterminal, alpha, beta, rfl, ?_⟩
  change markProductivePrefix alpha = alpha at hstable
  simp [hstable]

public theorem composite_plainPushSkip_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, beta⟩⟩ := by
  exact ⟨.plainPushSkip A B f, hpush, alpha, beta, rfl, rfl⟩

public theorem composite_matchTerminal_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (a : T) (inputPos : ℕ) (alpha : List (WorkSym g))
    (Z : WorkSym g) (beta : List (WorkSym g))
    (hinput : input[inputPos]? = some a) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .terminal a, Z :: beta⟩⟩
      ⟨inputPos + 1, ⟨alpha ++ [.dollar], Z, beta⟩⟩ := by
  exact ⟨.matchTerminal a, hinput, alpha, Z, beta, rfl, rfl⟩

/-- Mutual plain/live execution statement used by the singleton scheduler.  A plain task uses
none of its inherited stack.  A live task uses exactly the nonempty prefix `visible`; its
singleton layout may cross `close` markers but not another selected index or an open `$`.
Every selected token is used at the endpoint. -/
public theorem NFParse.singleton_runs
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) :
    (∀ (_unused : ¬ parse.ConsumesAt 0) (pre post : List T)
        (alpha : List (WorkSym g)) (next : WorkSym g)
        (tail : List (WorkSym g)), StablePrefix alpha →
      Relation.ReflTransGen (CompositeStep g (pre ++ w ++ post))
        ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
        (wordConfig g (pre ++ w).length alpha (next :: tail))) ∧
    (∀ (visible hidden : List g.flag) (word used : List (WorkSym g)),
      stack = visible ++ hidden → visible ≠ [] →
      (∀ k < visible.length, parse.ConsumesAt k) →
      (¬ parse.ConsumesAt visible.length) →
      SingletonLayout g visible word used →
      ∀ (pre post : List T) (alpha : List (WorkSym g)), StablePrefix alpha →
      Relation.ReflTransGen (CompositeStep g (pre ++ w ++ post))
        ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
        (wordConfig g (pre ++ w).length alpha used)) := by
  induction parse with
  | @binary A B C stack u v r hr hlhs hc hrhs left right ihleft ihright =>
      constructor
      · intro unused pre post alpha next tail hstable
        let input := pre ++ (u ++ v) ++ post
        let c₀ : Config g :=
          ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
        let c₁ : Config g :=
          ⟨pre.length, ⟨alpha ++ [.dollar], .plain B,
            .plain C :: next :: tail⟩⟩
        let c₂ : Config g :=
          ⟨(pre ++ u).length, ⟨alpha ++ [.dollar], .plain C, next :: tail⟩⟩
        have hstep : CompositeStep g input c₀ c₁ := by
          exact composite_plainBinary_stable input
            (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
            pre.length alpha (next :: tail) hstable
        have hleft := ihleft.1 (fun h => unused (Or.inl h))
          pre (v ++ post) alpha (.plain C) (next :: tail) hstable
        have hleft' : Relation.ReflTransGen (CompositeStep g input) c₁ c₂ := by
          simpa [input, c₁, c₂, wordConfig, List.append_assoc] using hleft
        have hright := ihright.1 (fun h => unused (Or.inr h))
          (pre ++ u) post alpha next tail hstable
        have hright' : Relation.ReflTransGen (CompositeStep g input) c₂
            (wordConfig g (pre ++ (u ++ v)).length alpha (next :: tail)) := by
          simpa [input, c₂, List.append_assoc] using hright
        exact (Relation.ReflTransGen.single hstep).trans (hleft'.trans hright')
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        let n := visible.length
        have hnpos : 0 < n := by
          exact List.length_pos_of_ne_nil hne
        have hboundLeft : ¬ left.ConsumesAt n := by
          intro h
          exact hboundary (Or.inl h)
        have hboundRight : ¬ right.ConsumesAt n := by
          intro h
          exact hboundary (Or.inr h)
        rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix left n hboundLeft with
          ⟨ml, hml, hallLeft, hfirstLeft⟩
        rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix right n hboundRight with
          ⟨mr, hmr, hallRight, hfirstRight⟩
        have hfull : ml = n ∨ mr = n := by
          have hdeep := hall (n - 1) (by omega)
          rcases hdeep with hdeep | hdeep
          · left
            have hlt : n - 1 < ml := by
              by_contra hnot
              have hle : ml ≤ n - 1 := Nat.le_of_not_gt hnot
              exact hfirstLeft (left.consumesAt_mono hle hdeep)
            omega
          · right
            have hlt : n - 1 < mr := by
              by_contra hnot
              have hle : mr ≤ n - 1 := Nat.le_of_not_gt hnot
              exact hfirstRight (right.consumesAt_mono hle hdeep)
            omega
        let leftSym : WorkSym g := if ml = 0 then .plain B else .live B
        let rightSym : WorkSym g := if mr = 0 then .plain C else .live C
        have hword : word ≠ [] := layout.input_ne_nil hne
        cases hwordEq : word with
        | nil => exact False.elim (hword hwordEq)
        | cons Z beta =>
          let input := pre ++ (u ++ v) ++ post
          let c₀ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
          let c₁ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], leftSym, rightSym :: word⟩⟩
          have hs : markProductivePrefix alpha = alpha := hstable
          have hstep : CompositeStep g input c₀ c₁ := by
            by_cases hml0 : ml = 0
            · by_cases hmr0 : mr = 0
              · have hp0 := hall 0 hnpos
                rcases hp0 with hp0 | hp0
                · exact False.elim (hfirstLeft (by simpa [hml0] using hp0))
                · exact False.elim (hfirstRight (by simpa [hmr0] using hp0))
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryRight_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
            · by_cases hmr0 : mr = 0
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryLeft_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryBoth_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
          rcases hfull with hleftFull | hrightFull
          · subst ml
            have hleftLayout : SingletonLayout g visible
                (rightSym :: word) (rightSym :: used) := by
              simpa using layout.prepend [rightSym]
                (by
                  by_cases h : mr = 0 <;> simp [IndexFree, rightSym, h])
                (by
                  by_cases h : mr = 0 <;> simp [DollarFree, rightSym, h])
            have hleftRun := ihleft.2 visible hidden (rightSym :: word)
              (rightSym :: used) hstack hne
              (by simpa [n] using hallLeft) (by simpa [n] using hfirstLeft)
              hleftLayout pre (v ++ post) alpha hstable
            have hleftRun' : Relation.ReflTransGen (CompositeStep g input) c₁
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], rightSym, used⟩⟩ := by
              simpa [input, c₁, leftSym, rightSym, n, hnpos.ne', wordConfig,
                List.append_assoc] using hleftRun
            have hrightRun : Relation.ReflTransGen (CompositeStep g input)
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], rightSym, used⟩⟩
                (wordConfig g (pre ++ (u ++ v)).length alpha used) := by
              by_cases hmr0 : mr = 0
              · have run := ihright.1 (by simpa [hmr0] using hfirstRight)
                    (pre ++ u) post alpha
                    (match used with | [] => .hash | z :: _ => z)
                    (match used with | [] => [] | _ :: zs => zs) hstable
                cases husedEq : used with
                | nil => exact False.elim (layout.output_ne_nil hne husedEq)
                | cons z zs =>
                  simpa [input, rightSym, hmr0, husedEq, wordConfig,
                    List.append_assoc] using
                      (ihright.1 (by simpa [hmr0] using hfirstRight)
                        (pre ++ u) post alpha z zs hstable)
              · have hvis : visible.take mr ≠ [] := by
                    apply List.ne_nil_of_length_pos
                    simp only [List.length_take]
                    omega
                have hmr' : mr ≤ visible.length := by simpa [n] using hmr
                have hstackRight : stack = visible.take mr ++
                    (visible.drop mr ++ hidden) := by
                  calc
                    stack = visible ++ hidden := hstack
                    _ = visible.take mr ++ (visible.drop mr ++ hidden) := by
                      rw [← List.append_assoc, List.take_append_drop]
                have hrightLayout := layout.idempotentTake mr
                have hallRight' : ∀ k < (visible.take mr).length,
                    right.ConsumesAt k := by
                  intro k hk
                  apply hallRight k
                  rwa [List.length_take, Nat.min_eq_left hmr'] at hk
                have run := ihright.2 (visible.take mr)
                  (visible.drop mr ++ hidden) used used hstackRight hvis
                  hallRight' (by
                    rwa [List.length_take, Nat.min_eq_left hmr'])
                  hrightLayout (pre ++ u) post alpha hstable
                simpa [input, rightSym, hmr0, wordConfig, List.append_assoc] using run
            simpa [input, c₀, hwordEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hleftRun'.trans hrightRun)
          · subst mr
            obtain ⟨middle, hleftRun, hremain⟩ :
                ∃ middle,
                  Relation.ReflTransGen (CompositeStep g input) c₁
                    ⟨(pre ++ u).length,
                      ⟨alpha ++ [.dollar], .live C, middle⟩⟩ ∧
                    SingletonLayout g visible middle used := by
              by_cases hml0 : ml = 0
              · have hplain := ihleft.1 (by simpa [hml0] using hfirstLeft)
                    pre (v ++ post) alpha (.live C) word hstable
                refine ⟨word, ?_, layout⟩
                simpa [input, c₁, leftSym, rightSym, hml0, n, hnpos.ne',
                  wordConfig, List.append_assoc] using hplain
              · rcases layout.splitTake ml with ⟨middle, hprefix, hremain⟩
                have hvis : visible.take ml ≠ [] := by
                  apply List.ne_nil_of_length_pos
                  simp only [List.length_take]
                  omega
                have hml' : ml ≤ visible.length := by simpa [n] using hml
                have hstackLeft : stack = visible.take ml ++
                    (visible.drop ml ++ hidden) := by
                  calc
                    stack = visible ++ hidden := hstack
                    _ = visible.take ml ++ (visible.drop ml ++ hidden) := by
                      rw [← List.append_assoc, List.take_append_drop]
                have hpending : SingletonLayout g (visible.take ml)
                    (.live C :: word) (.live C :: middle) := by
                  simpa using hprefix.prepend [.live C]
                    (by simp [IndexFree]) (by simp [DollarFree])
                have run := ihleft.2 (visible.take ml)
                  (visible.drop ml ++ hidden) (.live C :: word) (.live C :: middle)
                  hstackLeft hvis (by
                    intro k hk
                    apply hallLeft k
                    rwa [List.length_take, Nat.min_eq_left hml'] at hk)
                  (by
                    rwa [List.length_take, Nat.min_eq_left hml']) hpending
                  pre (v ++ post) alpha hstable
                refine ⟨middle, ?_, hremain⟩
                simpa [input, c₁, leftSym, rightSym, hml0, n, hnpos.ne',
                  wordConfig, List.append_assoc] using run
            have hrightRun := ihright.2 visible hidden middle used hstack hne
              (by simpa [n] using hallRight) (by simpa [n] using hfirstRight)
              hremain (pre ++ u) post alpha hstable
            have hrightRun' : Relation.ReflTransGen (CompositeStep g input)
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], .live C, middle⟩⟩
                (wordConfig g (pre ++ (u ++ v)).length alpha used) := by
              simpa [input, List.append_assoc] using hrightRun
            simpa [input, c₀, hwordEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hleftRun.trans hrightRun')
  | @pop A B f stack w r hr hlhs hc hrhs rest ih =>
      constructor
      · intro unused
        exact False.elim (unused (by simp [NFParse.ConsumesAt]))
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        cases visible with
        | nil => exact False.elim (hne rfl)
        | cons f' visible =>
          have hheads : f = f' := (List.cons.inj hstack).1
          have htails : stack = visible ++ hidden := (List.cons.inj hstack).2
          subst f'
          cases layout with
          | @cons _ _ beta tail tail' d hindex hdollar hlater tailLayout =>
            let input := pre ++ w ++ post
            let selected := WorkSym.index (cflagBase g f) d.markUsed
            let innerAlpha := alpha ++ [.dollar] ++ beta ++ [selected]
            have hinnerStable : StablePrefix innerAlpha := by
              exact stablePrefix_append_usedIndex
                (alpha ++ [.dollar] ++ beta) (cflagBase g f) d
            have hallRest : ∀ k < visible.length, rest.ConsumesAt k := by
              intro k hk
              have hp := hall (k + 1) (by simp; omega)
              simpa [NFParse.ConsumesAt] using hp
            have hboundaryRest : ¬ rest.ConsumesAt visible.length := by
              intro hrest
              apply hboundary
              simpa [NFParse.ConsumesAt, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hrest
            have hpop : CompositeStep g input
                ⟨pre.length, ⟨alpha ++ [.dollar], .live A,
                  beta ++ .index (cflagBase g f) d :: tail⟩⟩
                ⟨pre.length, ⟨innerAlpha ++ [.dollar],
                  (if visible = [] then .plain B else .live B),
                  .close :: tail⟩⟩ := by
              by_cases hvis : visible = []
              · subst visible
                simpa [input, innerAlpha, selected] using
                  composite_popPlain_at input (cflagBase g f) d
                    (cflagBase_edge_of_nfparse_pop hr hlhs hc hrhs rest)
                    pre.length alpha beta tail hindex
              · have hlater : d.later = true := hlater hvis
                simpa [input, innerAlpha, selected, hvis] using
                  composite_popLive_at input (cflagBase g f) d
                    (cflagBase_edge_of_nfparse_pop hr hlhs hc hrhs rest)
                    hlater pre.length alpha beta tail hindex
            have hinside : Relation.ReflTransGen (CompositeStep g input)
                ⟨pre.length, ⟨innerAlpha ++ [.dollar],
                  (if visible = [] then .plain B else .live B),
                  .close :: tail⟩⟩
                ⟨(pre ++ w).length,
                  ⟨innerAlpha ++ [.dollar], .close, tail'⟩⟩ := by
              by_cases hvis : visible = []
              · subst visible
                cases tailLayout
                have hrun := ih.1 (by simpa using hboundaryRest)
                  pre post innerAlpha .close tail hinnerStable
                simpa [input, wordConfig] using hrun
              · have hvisible : visible ≠ [] := hvis
                have crossed : SingletonLayout g visible
                    (.close :: tail) (.close :: tail') := by
                  simpa using tailLayout.prepend [.close]
                    (by simp [IndexFree]) (by simp [DollarFree])
                have hrun := ih.2 visible hidden (.close :: tail)
                  (.close :: tail') htails hvisible hallRest hboundaryRest
                  crossed pre post innerAlpha hinnerStable
                simpa [input, wordConfig, hvis] using hrun
            have hreturn : CompositeStep g input
                ⟨(pre ++ w).length,
                  ⟨innerAlpha ++ [.dollar], .close, tail'⟩⟩
                (wordConfig g (pre ++ w).length alpha
                  (beta ++ selected :: tail')) := by
              cases beta with
              | nil =>
                  simpa [innerAlpha, selected, wordConfig] using
                    composite_returnFrame_at input (pre ++ w).length alpha selected
                      [] tail' (by simp [selected]) (by simp [DollarFree])
              | cons z zs =>
                  have hz : z ≠ WorkSym.dollar := by
                    intro hz
                    subst z
                    exact hdollar (by simp)
                  have hfree : DollarFree (zs ++ [selected]) := by
                    apply DollarFree.append
                    · intro hm
                      exact hdollar (by simp [hm])
                    · simp [DollarFree, selected]
                  simpa [innerAlpha, selected, wordConfig, List.append_assoc] using
                    composite_returnFrame_at input (pre ++ w).length alpha z
                      (zs ++ [selected]) tail' hz hfree
            have hallrun := (Relation.ReflTransGen.single hpop).trans
              (hinside.trans (Relation.ReflTransGen.single hreturn))
            simpa [input, selected, wordConfig] using hallrun
  | @push A B f stack w r hr hlhs hc hrhs rest ih =>
      constructor
      · intro unused pre post alpha next tail hstable
        by_cases htop : rest.ConsumesAt 0
        · let input := pre ++ w ++ post
          let token := WorkSym.index (cflagBase g f) .firstPending
          let tokenUsed := WorkSym.index (cflagBase g f) .firstUsed
          let c₁ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: next :: tail⟩⟩
          have hstep : CompositeStep g input
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩ c₁ :=
            composite_plainPushUse_at input
              (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
              pre.length alpha (next :: tail)
          have hlayout : SingletonLayout g [f]
              (token :: next :: tail) (tokenUsed :: next :: tail) := by
            exact .cons (f := f) (beta := []) (d := .firstPending)
              (by simp [IndexFree]) (by simp [DollarFree])
              (by simp) (.nil (next :: tail))
          have hboundary : ¬ rest.ConsumesAt 1 := by
            simpa [NFParse.ConsumesAt] using unused
          have hrun := ih.2 [f] stack (token :: next :: tail)
            (tokenUsed :: next :: tail) (by simp) (by simp)
            (by
              intro k hk
              have hk0 : k = 0 := by simp at hk; omega
              simpa [hk0] using htop)
            (by simpa using hboundary) hlayout pre post alpha hstable
          have hrun' : Relation.ReflTransGen (CompositeStep g input) c₁
              ⟨(pre ++ w).length,
                ⟨alpha ++ [.dollar], tokenUsed, next :: tail⟩⟩ := by
            simpa [input, c₁, tokenUsed, wordConfig] using hrun
          have herase : CompositeStep g input
              ⟨(pre ++ w).length,
                ⟨alpha ++ [.dollar], tokenUsed, next :: tail⟩⟩
              (wordConfig g (pre ++ w).length alpha (next :: tail)) := by
            simpa [tokenUsed, wordConfig] using
              composite_eraseIndex_at input (cflagBase g f) .firstUsed rfl
                (pre ++ w).length alpha next tail
          exact (Relation.ReflTransGen.single hstep).trans
            (hrun'.trans (Relation.ReflTransGen.single herase))
        · have hstep : CompositeStep g (pre ++ w ++ post)
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain B, next :: tail⟩⟩ :=
            composite_plainPushSkip_stable (pre ++ w ++ post)
              (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
              pre.length alpha (next :: tail)
          exact (Relation.ReflTransGen.single hstep).trans
            (ih.1 htop pre post alpha next tail hstable)
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        have hword : word ≠ [] := layout.input_ne_nil hne
        have hused : used ≠ [] := layout.output_ne_nil hne
        cases hwordEq : word with
        | nil => exact False.elim (hword hwordEq)
        | cons Z beta =>
          cases husedEq : used with
          | nil => exact False.elim (hused husedEq)
          | cons Z' beta' =>
            let input := pre ++ w ++ post
            let token := WorkSym.index (cflagBase g f) .laterPending
            let tokenUsed := WorkSym.index (cflagBase g f) .laterUsed
            have hlayout : SingletonLayout g (f :: visible)
                (token :: word) (tokenUsed :: used) := by
              exact .cons (f := f) (beta := []) (d := .laterPending)
                (by simp [IndexFree]) (by simp [DollarFree])
                (fun _ => rfl) layout
            have hstack' : f :: stack = (f :: visible) ++ hidden := by
              simp [hstack]
            have hall' : ∀ k < (f :: visible).length, rest.ConsumesAt k := by
              intro k hk
              cases k with
              | zero =>
                  have hp0 : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt 0 :=
                    hall 0 (List.length_pos_of_ne_nil hne)
                  have hr1 : rest.ConsumesAt 1 := hp0
                  exact rest.consumesAt_of_consumesAt_succ 0 hr1
              | succ k =>
                  have hk' : k < visible.length := by simpa using hk
                  exact hall k hk'
            have hboundary' : ¬ rest.ConsumesAt (f :: visible).length := by
              simpa [NFParse.ConsumesAt] using hboundary
            have hstep : CompositeStep g input
                ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
                ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: word⟩⟩ := by
              simpa [input, token, hwordEq] using
                composite_livePushFresh_at input
                  (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                  pre.length alpha Z beta
            have hrun := ih.2 (f :: visible) hidden (token :: word)
              (tokenUsed :: used) hstack' (by simp) hall' hboundary'
              hlayout pre post alpha hstable
            have hrun' : Relation.ReflTransGen (CompositeStep g input)
                ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: word⟩⟩
                ⟨(pre ++ w).length,
                  ⟨alpha ++ [.dollar], tokenUsed, used⟩⟩ := by
              simpa [input, token, tokenUsed, wordConfig] using hrun
            have herase : CompositeStep g input
                ⟨(pre ++ w).length,
                  ⟨alpha ++ [.dollar], tokenUsed, used⟩⟩
                (wordConfig g (pre ++ w).length alpha used) := by
              simpa [tokenUsed, wordConfig, husedEq] using
                composite_eraseIndex_at input (cflagBase g f) .laterUsed rfl
                  (pre ++ w).length alpha Z' beta'
            simpa [input, hwordEq, husedEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hrun'.trans (Relation.ReflTransGen.single herase))
  | @terminal A stack a r hr hlhs hc hrhs =>
      constructor
      · intro _unused pre post alpha next tail hstable
        have hterminal := composite_plainTerminal_stable
          (pre ++ [a] ++ post) (terminalRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
          pre.length alpha (next :: tail) hstable
        have hinput : (pre ++ [a] ++ post)[pre.length]? = some a := by simp
        have hmatch := composite_matchTerminal_at (pre ++ [a] ++ post)
          a pre.length alpha next tail hinput
        simpa [wordConfig, List.append_assoc] using
          (Relation.ReflTransGen.single hterminal).trans
            (Relation.ReflTransGen.single hmatch)
      · intro visible hidden word used hstack hne hall
        exact False.elim (by
          have := hall 0 (List.length_pos_of_ne_nil hne)
          simp [NFParse.ConsumesAt] at this)

/-- Every concrete normal-form parse has an ordinary accepting run of Aho's composite machine.
This is the unconditional semantic completeness theorem; the later accounting refinement only
strengthens the same construction with a uniform work bound. -/
public theorem complete_of_nfparse
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (parse : NFParse g g.initial [] input) :
    Relation.ReflTransGen (CompositeStep g input)
      (initialConfig g) (finalConfig g input.length) := by
  have hrun := (IndexedGrammar.Aho.NFParse.singleton_runs parse).1
    (parse.not_consumesAt_of_stack_nil 0)
    [] [] [] WorkSym.hash [] (stablePrefix_nil g)
  simpa [initialConfig, finalConfig, wordConfig] using hrun


end Aho
end IndexedGrammar
