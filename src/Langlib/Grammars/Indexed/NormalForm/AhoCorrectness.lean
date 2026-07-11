module

public import Langlib.Grammars.Indexed.NormalForm.AhoCertificate
public import Langlib.Grammars.Indexed.NormalForm.AhoCompression
public import Langlib.Grammars.Indexed.NormalForm.AhoAccounting
public import Langlib.Grammars.Indexed.NormalForm.AhoMachine

@[expose]
public section

/-!
# Correctness scaffolding for Aho's composite machine

This file connects the data-carrying normal-form parse certificates to the composite moves from
`AhoMachine.lean`.  The full marked-index scheduler additionally needs a provenance-preserving
choice of relevant flag occurrences and the terminal-position injection described by Aho.  The
results below establish the generic bounded-reachability interface and give a complete bounded
simulation of the entire pop-free fragment.  Unlike a toy rule-by-rule statement, the fragment
theorem recursively schedules binary subparses, consumes the input in order, reaches the actual
final configuration, and bounds every intermediate logical work word.

The step constructor lemmas are intentionally phrased independently of the fragment and are the
entry points for extending the recursion with live-index frames.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Reachability with an invariant on every intermediate configuration -/

/-- The logical work word of a configuration fits in `bound` squares. -/
public def Config.Within {g : IndexedGrammar T} (bound : ℕ) (c : Config g) : Prop :=
  c.work.word.length ≤ bound

/-- Composite reachability whose initial configuration and both endpoints of every traversed
edge satisfy the work-tape bound.  Consequently every intermediate configuration is bounded. -/
public def BoundedReaches (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (bound : ℕ) (c c' : Config g) : Prop :=
  c.Within bound ∧
    Relation.ReflTransGen
      (fun x y => CompositeStep g input x y ∧ x.Within bound ∧ y.Within bound) c c'

namespace BoundedReaches

public theorem refl {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c : Config g} (hc : c.Within bound) :
    BoundedReaches g input bound c c :=
  ⟨hc, Relation.ReflTransGen.refl⟩

public theorem single {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c c' : Config g} (hc : c.Within bound)
    (hstep : CompositeStep g input c c') (hc' : c'.Within bound) :
    BoundedReaches g input bound c c' :=
  ⟨hc, Relation.ReflTransGen.single ⟨hstep, hc, hc'⟩⟩

public theorem trans {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c₁ c₂ c₃ : Config g}
    (h₁₂ : BoundedReaches g input bound c₁ c₂)
    (h₂₃ : BoundedReaches g input bound c₂ c₃) :
    BoundedReaches g input bound c₁ c₃ :=
  ⟨h₁₂.1, h₁₂.2.trans h₂₃.2⟩

/-- Forget the invariant and retain ordinary composite reachability. -/
public theorem toReflTransGen {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {bound : ℕ} {c c' : Config g}
    (h : BoundedReaches g input bound c c') :
    Relation.ReflTransGen (CompositeStep g input) c c' := by
  exact h.2.mono (fun _ _ hstep => hstep.1)

/-- Increase the available work bound. -/
public theorem mono {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {small large : ℕ} (hsl : small ≤ large) {c c' : Config g}
    (h : BoundedReaches g input small c c') :
    BoundedReaches g input large c c' := by
  refine ⟨le_trans h.1 hsl, ?_⟩
  exact h.2.mono (fun _ _ hstep =>
    ⟨hstep.1, le_trans hstep.2.1 hsl, le_trans hstep.2.2 hsl⟩)

end BoundedReaches

/-! ## Canonical plain-task configurations -/

/-- A plain nonterminal task at the top-level frame, followed by a nonempty continuation. -/
public def plainConfig (g : IndexedGrammar T) (inputPos : ℕ) (A : g.nt)
    (next : WorkSym g) (rest : List (WorkSym g)) : Config g :=
  ⟨inputPos, ⟨[WorkSym.dollar], WorkSym.plain A, next :: rest⟩⟩

/-- A terminal ready to be compared, followed by a nonempty continuation. -/
public def terminalConfig (g : IndexedGrammar T) (inputPos : ℕ) (a : T)
    (next : WorkSym g) (rest : List (WorkSym g)) : Config g :=
  ⟨inputPos, ⟨[WorkSym.dollar], WorkSym.terminal a, next :: rest⟩⟩

/-- The continuation exposed after a completed task has been removed. -/
public def continuationConfig (g : IndexedGrammar T) (inputPos : ℕ)
    (next : WorkSym g) (rest : List (WorkSym g)) : Config g :=
  ⟨inputPos, ⟨[WorkSym.dollar], next, rest⟩⟩

@[simp] public theorem plainConfig_word_length (g : IndexedGrammar T) (inputPos : ℕ)
    (A : g.nt) (next : WorkSym g) (rest : List (WorkSym g)) :
    (plainConfig g inputPos A next rest).work.word.length = rest.length + 3 := by
  simp [plainConfig, WorkCursor.word]

@[simp] public theorem terminalConfig_word_length (g : IndexedGrammar T) (inputPos : ℕ)
    (a : T) (next : WorkSym g) (rest : List (WorkSym g)) :
    (terminalConfig g inputPos a next rest).work.word.length = rest.length + 3 := by
  simp [terminalConfig, WorkCursor.word]

@[simp] public theorem continuationConfig_word_length (g : IndexedGrammar T) (inputPos : ℕ)
    (next : WorkSym g) (rest : List (WorkSym g)) :
    (continuationConfig g inputPos next rest).work.word.length = rest.length + 2 := by
  simp [continuationConfig, WorkCursor.word]

/-! ## Certified constructors for the plain composite moves -/

public theorem composite_plainBinary {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {A B C : g.nt} (h : AugBinary g A B C)
    (inputPos : ℕ) (next : WorkSym g) (rest : List (WorkSym g)) :
    CompositeStep g input
      (plainConfig g inputPos A next rest)
      (plainConfig g inputPos B (WorkSym.plain C) (next :: rest)) := by
  refine ⟨CompositeCert.plainBinary A B C, h, [], next :: rest, ?_, ?_⟩
  · simp [plainConfig]
  · simp [plainConfig, markProductivePrefix]

public theorem composite_plainTerminal {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {A : g.nt} {a : T} (h : AugTerminal g A a)
    (inputPos : ℕ) (next : WorkSym g) (rest : List (WorkSym g)) :
    CompositeStep g input
      (plainConfig g inputPos A next rest)
      (terminalConfig g inputPos a next rest) := by
  refine ⟨CompositeCert.plainTerminal A a, h, [], next :: rest, ?_, ?_⟩
  · simp [plainConfig]
  · simp [plainConfig, terminalConfig, markProductivePrefix]

public theorem composite_plainPushSkip {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {A B : g.nt} {f : g.flag} (h : AugPush g A B f)
    (inputPos : ℕ) (next : WorkSym g) (rest : List (WorkSym g)) :
    CompositeStep g input
      (plainConfig g inputPos A next rest)
      (plainConfig g inputPos B next rest) := by
  refine ⟨CompositeCert.plainPushSkip A B f, h, [], next :: rest, ?_, ?_⟩
  · simp [plainConfig]
  · simp [plainConfig]

public theorem composite_matchTerminal {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {a : T} {inputPos : ℕ}
    (hinput : input[inputPos]? = some a)
    (next : WorkSym g) (rest : List (WorkSym g)) :
    CompositeStep g input
      (terminalConfig g inputPos a next rest)
      (continuationConfig g (inputPos + 1) next rest) := by
  refine ⟨CompositeCert.matchTerminal a, hinput, [], next, rest, ?_, ?_⟩
  · simp [terminalConfig]
  · simp [terminalConfig, continuationConfig]

/-! ## Grammar effect of every composite certificate -/

/-- The local indexed-grammar effect named by a composite certificate.  Structural tape moves
have no grammar effect.  A pop certificate is sound for every concrete flag string denoted by its
compressed relation. -/
public def CompositeCert.GrammarSound {g : IndexedGrammar T} [Fintype g.nt] :
    CompositeCert g → Prop
  | .plainBinary A B C | .liveBinaryBoth A B C |
      .liveBinaryLeft A B C | .liveBinaryRight A B C =>
      AugBinary g A B C → ∀ suffix,
        g.Derives [ISym.indexed A suffix]
          [ISym.indexed B suffix, ISym.indexed C suffix]
  | .plainTerminal A a =>
      AugTerminal g A a → ∀ suffix,
        g.Derives [ISym.indexed A suffix] [ISym.terminal a]
  | .plainPushSkip A B f | .plainPushUse A B f | .livePushFresh A B f =>
      AugPush g A B f → ∀ suffix,
        g.Derives [ISym.indexed A suffix] [ISym.indexed B (f :: suffix)]
  | .livePushCompress A B f _ _ =>
      AugPush g A B f → ∀ suffix,
        g.Derives [ISym.indexed A suffix] [ISym.indexed B (f :: suffix)]
  | .popPlain R _ A B | .popLive R _ A B =>
      ∀ flags, CFlag.Denotes g flags R → R A B = true → ∀ suffix,
        g.Derives [ISym.indexed A (flags ++ suffix)] [ISym.indexed B suffix]
  | .matchTerminal _ | .eraseIndex _ _ | .returnFrame => True

/-- Each finite certificate is locally sound for the indexed grammar, independently of the tape
contexts in which the corresponding composite move is applied. -/
public theorem compositeCert_grammarSound {g : IndexedGrammar T} [Fintype g.nt]
    (cert : CompositeCert g) : cert.GrammarSound := by
  cases cert with
  | plainBinary A B C =>
      intro h suffix
      exact augBinary_derives h suffix
  | plainTerminal A a =>
      intro h suffix
      exact augTerminal_derives h suffix
  | plainPushSkip A B f =>
      intro h suffix
      exact augPush_derives h suffix
  | plainPushUse A B f =>
      intro h suffix
      exact augPush_derives h suffix
  | liveBinaryBoth A B C =>
      intro h suffix
      exact augBinary_derives h suffix
  | liveBinaryLeft A B C =>
      intro h suffix
      exact augBinary_derives h suffix
  | liveBinaryRight A B C =>
      intro h suffix
      exact augBinary_derives h suffix
  | livePushFresh A B f =>
      intro h suffix
      exact augPush_derives h suffix
  | livePushCompress A B f R d =>
      intro h suffix
      exact augPush_derives h suffix
  | popPlain R d A B =>
      intro flags hden hedge suffix
      exact hden.edge_derives hedge suffix
  | popLive R d A B =>
      intro flags hden hedge suffix
      exact hden.edge_derives hedge suffix
  | matchTerminal a => trivial
  | eraseIndex R d => trivial
  | returnFrame => trivial

/-! ## Provenance of compressed relations -/

/-- Every compressed-index occurrence in a work-word denotes some concrete, nonempty string of
grammar flags.  The concrete string is ghost data: the finite machine stores only its relation. -/
public def WorkIndexProvenance {g : IndexedGrammar T} [Fintype g.nt] :
    List (WorkSym g) → Prop
  | [] => True
  | WorkSym.index R _ :: rest =>
      (∃ flags, CFlag.Denotes g flags R) ∧ WorkIndexProvenance rest
  | _ :: rest => WorkIndexProvenance rest

@[simp] public theorem workIndexProvenance_nil {g : IndexedGrammar T} [Fintype g.nt] :
    WorkIndexProvenance ([] : List (WorkSym g)) :=
  trivial

@[simp] public theorem workIndexProvenance_terminal_cons
    {g : IndexedGrammar T} [Fintype g.nt] (a : T) (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.terminal a :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_plain_cons
    {g : IndexedGrammar T} [Fintype g.nt] (A : g.nt) (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.plain A :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_live_cons
    {g : IndexedGrammar T} [Fintype g.nt] (A : g.nt) (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.live A :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_index_cons
    {g : IndexedGrammar T} [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.index R d :: xs) ↔
      (∃ flags, CFlag.Denotes g flags R) ∧ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_dollar_cons
    {g : IndexedGrammar T} [Fintype g.nt] (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.dollar :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_close_cons
    {g : IndexedGrammar T} [Fintype g.nt] (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.close :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_hash_cons
    {g : IndexedGrammar T} [Fintype g.nt] (xs : List (WorkSym g)) :
    WorkIndexProvenance (WorkSym.hash :: xs) ↔ WorkIndexProvenance xs :=
  Iff.rfl

@[simp] public theorem workIndexProvenance_append
    {g : IndexedGrammar T} [Fintype g.nt] (xs ys : List (WorkSym g)) :
    WorkIndexProvenance (xs ++ ys) ↔
      WorkIndexProvenance xs ∧ WorkIndexProvenance ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp [WorkIndexProvenance, ih, and_assoc]

/-- Split provenance of an arbitrary head symbol from its tail. -/
public theorem workIndexProvenance_cons
    {g : IndexedGrammar T} [Fintype g.nt] (z : WorkSym g) (xs : List (WorkSym g)) :
    WorkIndexProvenance (z :: xs) ↔
      WorkIndexProvenance [z] ∧ WorkIndexProvenance xs := by
  simpa using workIndexProvenance_append [z] xs

@[simp] public theorem workIndexProvenance_reverse
    {g : IndexedGrammar T} [Fintype g.nt] (xs : List (WorkSym g)) :
    WorkIndexProvenance xs.reverse ↔ WorkIndexProvenance xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.reverse_cons, workIndexProvenance_append, ih]
      cases x <;> simp [WorkIndexProvenance, and_comm]

/-- Productive marking changes only an index mark, never the represented relation. -/
@[simp] public theorem workIndexProvenance_markProductivePrefix
    {g : IndexedGrammar T} [Fintype g.nt] (alpha : List (WorkSym g)) :
    WorkIndexProvenance (markProductivePrefix alpha) ↔ WorkIndexProvenance alpha := by
  unfold markProductivePrefix
  cases hrev : alpha.reverse with
  | nil =>
      have halpha : alpha = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      simp [halpha]
  | cons z zs =>
      cases z with
      | index R d =>
          have halpha : alpha = (WorkSym.index R d :: zs).reverse := by
            rw [← hrev, List.reverse_reverse]
          subst alpha
          simp [WorkIndexProvenance]
      | terminal a => simp
      | plain A => simp
      | live A => simp
      | dollar => simp
      | close => simp
      | hash => simp

/-- Configuration-level compressed-index provenance. -/
public def Config.IndexProvenance {g : IndexedGrammar T} [Fintype g.nt]
    (c : Config g) : Prop :=
  WorkIndexProvenance c.work.word

public theorem initialConfig_indexProvenance (g : IndexedGrammar T) [Fintype g.nt] :
    (initialConfig g).IndexProvenance := by
  simp [Config.IndexProvenance, initialConfig, WorkCursor.word]

/-- Every composite move preserves concrete-string provenance of all compressed relations. -/
public theorem certStep_preserves_indexProvenance
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) {c c' : Config g}
    (hstep : CertStep g input cert c c')
    (hprov : c.IndexProvenance) : c'.IndexProvenance := by
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨_haug, alpha, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | plainTerminal A a =>
      rcases hstep with ⟨_haug, alpha, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | plainPushSkip A B f =>
      rcases hstep with ⟨_haug, alpha, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | plainPushUse A B f =>
      rcases hstep with ⟨_haug, alpha, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simp only [Config.IndexProvenance, WorkCursor.word,
        workIndexProvenance_append, workIndexProvenance_dollar_cons,
        workIndexProvenance_live_cons, workIndexProvenance_index_cons] at hprov ⊢
      exact ⟨hprov.1, ⟨⟨[f], CFlag.Denotes.base f⟩, hprov.2⟩⟩
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨_haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨_haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | liveBinaryRight A B C =>
      rcases hstep with ⟨_haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | livePushFresh A B f =>
      rcases hstep with ⟨_haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simp only [Config.IndexProvenance, WorkCursor.word,
        workIndexProvenance_append, workIndexProvenance_dollar_cons,
        workIndexProvenance_live_cons, workIndexProvenance_index_cons] at hprov ⊢
      exact ⟨hprov.1, ⟨⟨[f], CFlag.Denotes.base f⟩, hprov.2⟩⟩
  | livePushCompress A B f R d =>
      rcases hstep with ⟨_haug, _hne, alpha, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simp only [Config.IndexProvenance, WorkCursor.word,
        workIndexProvenance_append, workIndexProvenance_dollar_cons,
        workIndexProvenance_live_cons, workIndexProvenance_index_cons] at hprov ⊢
      rcases hprov.2.1 with ⟨flags, hden⟩
      exact ⟨hprov.1, ⟨⟨[f] ++ flags,
        CFlag.Denotes.comp (CFlag.Denotes.base f) hden⟩, hprov.2.2⟩⟩
  | popPlain R d A B =>
      rcases hstep with ⟨_hedge, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _hfree, hc, hc'⟩
        rw [hc] at hprov
        rw [hc']
        simpa [Config.IndexProvenance, WorkCursor.word, List.append_assoc] using hprov
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hprov
        rw [hc']
        simp only [Config.IndexProvenance, WorkCursor.word,
          workIndexProvenance_append, workIndexProvenance_dollar_cons,
          workIndexProvenance_live_cons, workIndexProvenance_plain_cons,
          workIndexProvenance_index_cons] at hprov ⊢
        exact ⟨hprov.1, hprov.2.2⟩
  | popLive R d A B =>
      rcases hstep with ⟨_hedge, _hlater, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _hfree, hc, hc'⟩
        rw [hc] at hprov
        rw [hc']
        simpa [Config.IndexProvenance, WorkCursor.word, List.append_assoc] using hprov
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hprov
        rw [hc']
        simp only [Config.IndexProvenance, WorkCursor.word,
          workIndexProvenance_append, workIndexProvenance_dollar_cons,
          workIndexProvenance_live_cons, workIndexProvenance_index_cons] at hprov ⊢
        exact ⟨hprov.1, hprov.2.2⟩
  | matchTerminal a =>
      rcases hstep with ⟨_hinput, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simpa [Config.IndexProvenance, WorkCursor.word] using hprov
  | eraseIndex R d =>
      rcases hstep with ⟨_herase, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      simp only [Config.IndexProvenance, WorkCursor.word,
        workIndexProvenance_append, workIndexProvenance_dollar_cons,
        workIndexProvenance_index_cons] at hprov ⊢
      exact ⟨hprov.1, hprov.2.2⟩
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, _hZ, _hfree, hc, hc'⟩
      rw [hc] at hprov
      rw [hc']
      change WorkIndexProvenance
        ((alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar]) ++
          WorkSym.close :: gamma) at hprov
      change WorkIndexProvenance
        ((alpha ++ [WorkSym.dollar]) ++ Z :: (beta ++ gamma))
      have houter : WorkIndexProvenance alpha ∧
          WorkIndexProvenance
            (Z :: (beta ++ WorkSym.dollar :: WorkSym.close :: gamma)) := by
        simpa [workIndexProvenance_append, WorkIndexProvenance,
          List.append_assoc] using hprov
      have hzrest := (workIndexProvenance_cons Z
        (beta ++ WorkSym.dollar :: WorkSym.close :: gamma)).mp houter.2
      have htail : WorkIndexProvenance beta ∧ WorkIndexProvenance gamma := by
        simpa [workIndexProvenance_append, WorkIndexProvenance] using hzrest.2
      apply (workIndexProvenance_append (alpha ++ [WorkSym.dollar])
        (Z :: (beta ++ gamma))).mpr
      constructor
      · simpa [workIndexProvenance_append, WorkIndexProvenance] using houter.1
      · apply (workIndexProvenance_cons Z (beta ++ gamma)).mpr
        exact ⟨hzrest.1, (workIndexProvenance_append beta gamma).mpr htail⟩

/-- Composite-step wrapper for provenance preservation. -/
public theorem compositeStep_preserves_indexProvenance
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} (hstep : CompositeStep g input c c')
    (hprov : c.IndexProvenance) : c'.IndexProvenance := by
  rcases hstep with ⟨cert, hcert⟩
  exact certStep_preserves_indexProvenance input cert hcert hprov

/-- Every compressed-index member of a provenance-valid word has a concrete flag-string
denotation. -/
public theorem denotes_of_index_mem {g : IndexedGrammar T} [Fintype g.nt]
    {xs : List (WorkSym g)} (hprov : WorkIndexProvenance xs)
    {R : CFlag g} {d : IndexMark} (hmem : WorkSym.index R d ∈ xs) :
    ∃ flags, CFlag.Denotes g flags R := by
  induction xs with
  | nil => simp at hmem
  | cons z zs ih =>
      have hcases := List.mem_cons.mp hmem
      cases z with
      | index S e =>
          rcases hprov with ⟨hhead, htail⟩
          rcases hcases with heq | htailMem
          · cases heq
            exact hhead
          · exact ih htail htailMem
      | terminal a =>
          exact ih hprov (hcases.resolve_left (by simp))
      | plain A =>
          exact ih hprov (hcases.resolve_left (by simp))
      | live A =>
          exact ih hprov (hcases.resolve_left (by simp))
      | dollar =>
          exact ih hprov (hcases.resolve_left (by simp))
      | close =>
          exact ih hprov (hcases.resolve_left (by simp))
      | hash =>
          exact ih hprov (hcases.resolve_left (by simp))

public theorem Config.denotes_of_index_mem
    {g : IndexedGrammar T} [Fintype g.nt] {c : Config g}
    (hprov : c.IndexProvenance) {R : CFlag g} {d : IndexMark}
    (hmem : WorkSym.index R d ∈ c.work.word) :
    ∃ flags, CFlag.Denotes g flags R :=
  IndexedGrammar.Aho.denotes_of_index_mem hprov hmem

/-- Provenance therefore holds at every configuration reachable from the initial one. -/
public theorem reachable_indexProvenance
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T) {c : Config g}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c) :
    c.IndexProvenance := by
  induction hreach with
  | refl => exact initialConfig_indexProvenance g
  | tail _hprev hstep ih =>
      exact compositeStep_preserves_indexProvenance input hstep ih

/-- Every reachable `popPlain` move consumes a relation with concrete flag-string provenance and
has the corresponding indexed-grammar derivation effect. -/
public theorem reachable_popPlain_effect
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c)
    (hstep : CertStep g input (.popPlain R d A B) c c') :
    ∃ flags, CFlag.Denotes g flags R ∧
      ∀ suffix, g.Derives [ISym.indexed A (flags ++ suffix)]
        [ISym.indexed B suffix] := by
  rcases hstep with ⟨hedge, hframe | herase⟩
  · rcases hframe with ⟨alpha, beta, gamma, _hfree, hc, _hc'⟩
    have hmem : WorkSym.index R d ∈ c.work.word := by
      rw [hc]
      simp [WorkCursor.word]
    rcases Config.denotes_of_index_mem (reachable_indexProvenance input hreach) hmem with
      ⟨flags, hden⟩
    exact ⟨flags, hden, fun suffix => hden.edge_derives hedge suffix⟩
  · rcases herase with ⟨alpha, gamma, hc, _hc'⟩
    have hmem : WorkSym.index R d ∈ c.work.word := by
      rw [hc]
      simp [WorkCursor.word]
    rcases Config.denotes_of_index_mem (reachable_indexProvenance input hreach) hmem with
      ⟨flags, hden⟩
    exact ⟨flags, hden, fun suffix => hden.edge_derives hedge suffix⟩

/-- Every reachable `popLive` move likewise has a concrete indexed-grammar derivation effect. -/
public theorem reachable_popLive_effect
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c)
    (hstep : CertStep g input (.popLive R d A B) c c') :
    ∃ flags, CFlag.Denotes g flags R ∧
      ∀ suffix, g.Derives [ISym.indexed A (flags ++ suffix)]
        [ISym.indexed B suffix] := by
  rcases hstep with ⟨hedge, _hlater, hframe | herase⟩
  · rcases hframe with ⟨alpha, beta, gamma, _hfree, hc, _hc'⟩
    have hmem : WorkSym.index R d ∈ c.work.word := by
      rw [hc]
      simp [WorkCursor.word]
    rcases Config.denotes_of_index_mem (reachable_indexProvenance input hreach) hmem with
      ⟨flags, hden⟩
    exact ⟨flags, hden, fun suffix => hden.edge_derives hedge suffix⟩
  · rcases herase with ⟨alpha, gamma, hc, _hc'⟩
    have hmem : WorkSym.index R d ∈ c.work.word := by
      rw [hc]
      simp [WorkCursor.word]
    rcases Config.denotes_of_index_mem (reachable_indexProvenance input hreach) hmem with
      ⟨flags, hden⟩
    exact ⟨flags, hden, fun suffix => hden.edge_derives hedge suffix⟩

/-! ## Input-head safety -/

/-- The input cursor has not moved beyond the fixed input word. -/
public def Config.InputWithin {g : IndexedGrammar T} (input : List T) (c : Config g) : Prop :=
  c.inputPos ≤ input.length

public theorem initialConfig_inputWithin (g : IndexedGrammar T) (input : List T) :
    (initialConfig g).InputWithin input := by
  simp [Config.InputWithin, initialConfig]

/-- Every certified move preserves input-head safety.  The sole advancing move carries a
successful `getElem?` check, which proves that the old cursor is strictly inside the input. -/
public theorem certStep_preserves_inputWithin
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) {c c' : Config g}
    (hstep : CertStep g input cert c c') (hin : c.InputWithin input) :
    c'.InputWithin input := by
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainTerminal A a =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainPushSkip A B f =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | plainPushUse A B f =>
      rcases hstep with ⟨_, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | liveBinaryRight A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | livePushFresh A B f =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | livePushCompress A B f R d =>
      rcases hstep with ⟨_, _, alpha, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | popPlain R d A B =>
      rcases hstep with ⟨_, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
  | popLive R d A B =>
      rcases hstep with ⟨_, _, hframe | herase⟩
      · rcases hframe with ⟨alpha, beta, gamma, _, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hin
        rw [hc']
        exact hin
  | matchTerminal a =>
      rcases hstep with ⟨hinput, alpha, Z, beta, hc, hc'⟩
      have hlt : c.inputPos < input.length :=
        (List.getElem?_eq_some_iff.mp hinput).choose
      rw [hc']
      simp only [Config.InputWithin]
      omega
  | eraseIndex R d =>
      rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, _, _, hc, hc'⟩
      rw [hc] at hin
      rw [hc']
      exact hin

public theorem compositeStep_preserves_inputWithin
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} (hstep : CompositeStep g input c c')
    (hin : c.InputWithin input) : c'.InputWithin input := by
  rcases hstep with ⟨cert, hcert⟩
  exact certStep_preserves_inputWithin input cert hcert hin

public theorem reachable_inputWithin
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T) {c : Config g}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c) :
    c.InputWithin input := by
  induction hreach with
  | refl => exact initialConfig_inputWithin g input
  | tail _hprev hstep ih =>
      exact compositeStep_preserves_inputWithin input hstep ih

/-! ## A complete bounded simulation of the pop-free fragment -/

end Aho

namespace NFParse

/-- A concrete parse is pop-free when it never consumes a stack flag.  Push rules are allowed;
their flags are unused and are therefore taken through Aho's `plainPushSkip` move. -/
public def PopFree {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T} :
    NFParse g A σ w → Prop
  | .binary _ _ _ _ left right => left.PopFree ∧ right.PopFree
  | .pop .. => False
  | .push _ _ _ _ rest => rest.PopFree
  | .terminal .. => True

@[simp] public theorem popFree_binary_iff
    {g : IndexedGrammar T} {A B C : g.nt} {σ : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B σ u) (right : NFParse g C σ v) :
    (NFParse.binary hr hlhs hc hrhs left right).PopFree ↔
      left.PopFree ∧ right.PopFree :=
  Iff.rfl

@[simp] public theorem not_popFree_pop
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B ρ w) :
    ¬ (NFParse.pop hr hlhs hc hrhs rest).PopFree := by
  simp [PopFree]

@[simp] public theorem popFree_push_iff
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {σ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: σ) w) :
    (NFParse.push hr hlhs hc hrhs rest).PopFree ↔ rest.PopFree :=
  Iff.rfl

@[simp] public theorem popFree_terminal
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    (NFParse.terminal (σ := σ) hr hlhs hc hrhs).PopFree :=
  trivial

end NFParse

namespace Aho

/-- A pop-free parse can be run in front of any nonempty plain continuation.  The budget
`1 + |w| + |continuation|` counts the top-level `$`, at most one pending task per terminal leaf,
and the external continuation. -/
public theorem popFree_run_bounded {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) (hfree : p.PopFree)
    (pre post : List T) (next : WorkSym g) (rest : List (WorkSym g))
    (bound : ℕ)
    (hbound : 1 + w.length + (next :: rest).length ≤ bound) :
    BoundedReaches g (pre ++ w ++ post) bound
      (plainConfig g pre.length A next rest)
      (continuationConfig g (pre ++ w).length next rest) := by
  induction p generalizing pre post next rest bound with
  | @binary A0 B C stack u v r hr hlhs hc hrhs left right ihleft ihright =>
      rcases hfree with ⟨hfreeLeft, hfreeRight⟩
      have hleftPos : 0 < u.length := left.yield_length_pos
      have hrightPos : 0 < v.length := right.yield_length_pos
      let input := pre ++ (u ++ v) ++ post
      let c₀ := plainConfig g pre.length A0 next rest
      let c₁ := plainConfig g pre.length B (WorkSym.plain C) (next :: rest)
      have hc₀ : c₀.Within bound := by
        change (plainConfig g pre.length A0 next rest).work.word.length ≤ bound
        rw [plainConfig_word_length]
        simp [List.length_append] at hbound
        omega
      have hc₁ : c₁.Within bound := by
        change (plainConfig g pre.length B (WorkSym.plain C)
          (next :: rest)).work.word.length ≤ bound
        rw [plainConfig_word_length]
        simp [List.length_append] at hbound ⊢
        omega
      have hstep : CompositeStep g input c₀ c₁ := by
        dsimp [input, c₀, c₁]
        exact composite_plainBinary _ (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
          pre.length next rest
      have hfirst : BoundedReaches g input bound c₀ c₁ :=
        BoundedReaches.single hc₀ hstep hc₁
      have hboundLeft :
          1 + u.length + (WorkSym.plain C :: next :: rest).length ≤ bound := by
        simp [List.length_append] at hbound ⊢
        omega
      have hrunLeft := ihleft hfreeLeft pre (v ++ post) (WorkSym.plain C)
        (next :: rest) bound hboundLeft
      have hrunLeft' :
          BoundedReaches g input bound c₁
            (plainConfig g (pre ++ u).length C next rest) := by
        simpa [input, c₁, plainConfig, continuationConfig, List.append_assoc] using hrunLeft
      have hboundRight : 1 + v.length + (next :: rest).length ≤ bound := by
        simp [List.length_append] at hbound ⊢
        omega
      have hrunRight := ihright hfreeRight (pre ++ u) post next rest bound hboundRight
      have hrunRight' :
          BoundedReaches g input bound
            (plainConfig g (pre ++ u).length C next rest)
            (continuationConfig g (pre ++ u ++ v).length next rest) := by
        simpa [input, List.append_assoc] using hrunRight
      have hall := (hfirst.trans hrunLeft').trans hrunRight'
      simpa [input, c₀, List.append_assoc] using hall
  | @pop A0 B f rho yield r hr hlhs hc hrhs child ih =>
      exact False.elim hfree
  | @push A0 B f stack yield r hr hlhs hc hrhs child ih =>
      have hc₀ : (plainConfig g pre.length A0 next rest).Within bound := by
        change (plainConfig g pre.length A0 next rest).work.word.length ≤ bound
        rw [plainConfig_word_length]
        have hp : 0 < yield.length := child.yield_length_pos
        simp at hbound
        omega
      have hc₁ : (plainConfig g pre.length B next rest).Within bound := by
        change (plainConfig g pre.length B next rest).work.word.length ≤ bound
        rw [plainConfig_word_length]
        have hp : 0 < yield.length := child.yield_length_pos
        simp at hbound
        omega
      have hstep : CompositeStep g (pre ++ yield ++ post)
          (plainConfig g pre.length A0 next rest)
          (plainConfig g pre.length B next rest) :=
        composite_plainPushSkip (pre ++ yield ++ post)
          (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
          pre.length next rest
      have hfirst := BoundedReaches.single hc₀ hstep hc₁
      exact hfirst.trans (ih hfree pre post next rest bound hbound)
  | @terminal A0 stack a r hr hlhs hc hrhs =>
      have hc₀ : (plainConfig g pre.length A0 next rest).Within bound := by
        change (plainConfig g pre.length A0 next rest).work.word.length ≤ bound
        rw [plainConfig_word_length]
        simp at hbound
        omega
      have hc₁ : (terminalConfig g pre.length a next rest).Within bound := by
        change (terminalConfig g pre.length a next rest).work.word.length ≤ bound
        rw [terminalConfig_word_length]
        simp at hbound
        omega
      have hc₂ : (continuationConfig g (pre.length + 1) next rest).Within bound := by
        change (continuationConfig g (pre.length + 1) next rest).work.word.length ≤ bound
        rw [continuationConfig_word_length]
        simp at hbound
        omega
      have hterminal : CompositeStep g (pre ++ [a] ++ post)
          (plainConfig g pre.length A0 next rest)
          (terminalConfig g pre.length a next rest) :=
        composite_plainTerminal (pre ++ [a] ++ post)
          (terminalRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
          pre.length next rest
      have hinput : (pre ++ [a] ++ post)[pre.length]? = some a := by
        simp
      have hmatch : CompositeStep g (pre ++ [a] ++ post)
          (terminalConfig g pre.length a next rest)
          (continuationConfig g (pre.length + 1) next rest) :=
        composite_matchTerminal _ hinput next rest
      have hfirst := BoundedReaches.single hc₀ hterminal hc₁
      have hsecond := BoundedReaches.single hc₁ hmatch hc₂
      simpa [List.append_assoc] using hfirst.trans hsecond

/-- Initial-configuration completeness, including the `8*n` work bound, for every pop-free
normal-form parse. -/
public theorem popFree_complete_bounded {g : IndexedGrammar T} [Fintype g.nt]
    {w : List T} (p : NFParse g g.initial [] w) (hfree : p.PopFree) :
    BoundedReaches g w (12 * w.length)
      (initialConfig g) (finalConfig g w.length) := by
  have hpos : 0 < w.length := p.yield_length_pos
  have hbound : 1 + w.length + ([WorkSym.hash] : List (WorkSym g)).length ≤
      12 * w.length := by
    simp
    omega
  have hrun := popFree_run_bounded p hfree [] [] WorkSym.hash [] (12 * w.length) hbound
  simpa [plainConfig, continuationConfig, initialConfig, finalConfig] using hrun

/-- Ordinary accepting composite reachability for the pop-free fragment. -/
public theorem popFree_complete {g : IndexedGrammar T} [Fintype g.nt]
    {w : List T} (p : NFParse g g.initial [] w) (hfree : p.PopFree) :
    Relation.ReflTransGen (CompositeStep g w)
      (initialConfig g) (finalConfig g w.length) :=
  (popFree_complete_bounded p hfree).toReflTransGen

end Aho
end IndexedGrammar
