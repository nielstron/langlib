module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Pop

@[expose]
public section

/-!
# Exact scheduler moves

Invariant-ready constructors for each composite machine transition and stack-layout boundary.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Exact composite-move constructors -/

/-- Starting the first relevant stack block. -/
public theorem composite_plainPushUse_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagBase g f) .firstPending :: beta⟩⟩ := by
  exact ⟨.plainPushUse A B f, hpush, alpha, beta, rfl, rfl⟩

/-- A live binary task whose two children both consume the represented stack. -/
public theorem composite_liveBinaryBoth_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .live B,
        .live C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryBoth A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- A live binary task whose left child alone consumes the represented stack. -/
public theorem composite_liveBinaryLeft_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .live B,
        .plain C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryLeft A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- A live binary task whose right child alone consumes the represented stack. -/
public theorem composite_liveBinaryRight_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .plain B,
        .live C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryRight A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- Introduce a fresh relevant flag block above an already-live continuation. -/
public theorem composite_livePushFresh_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagBase g f) .laterPending :: Z :: beta⟩⟩ := by
  exact ⟨.livePushFresh A B f, hpush, alpha, Z, beta, rfl, rfl⟩

/-- Compress a new pushed flag into the adjacent represented block. -/
public theorem composite_livePushCompress_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (R : CFlag g) (d : IndexMark)
    (hpush : AugPush g A B f)
    (hne : (cflagComp g (cflagBase g f) R).Nonempty)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagComp g (cflagBase g f) R) d :: beta⟩⟩ := by
  exact ⟨.livePushCompress A B f R d, hpush, hne, alpha, beta, rfl, rfl⟩

/-- Consume a represented block and continue with a plain task in a fresh frame. -/
public theorem composite_popPlain_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩⟩ := by
  exact ⟨.popPlain R d A B, hedge,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

/-- Consume a represented block and continue with a live task in a fresh frame. -/
public theorem composite_popLive_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (hlater : d.later = true) (inputPos : ℕ)
    (alpha beta gamma : List (WorkSym g)) (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩⟩ := by
  exact ⟨.popLive R d A B, hedge, hlater,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

/-- Consume an adjacent compressed block and discard its token before entering a plain
residual task.  The adjacency is what makes deletion ownership-safe: no pending sibling lies
between the active task and the selected block. -/
public theorem composite_popPlainErase_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (inputPos : ℕ) (alpha gamma : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, gamma⟩⟩ := by
  exact ⟨.popPlain R d A B, hedge, Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

/-- Unframed adjacent pop whose residual task still consumes a represented suffix. -/
public theorem composite_popLiveErase_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (hlater : d.later = true) (inputPos : ℕ)
    (alpha gamma : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B, gamma⟩⟩ := by
  exact ⟨.popLive R d A B, hedge, hlater,
    Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

/-- Remove an erasable represented block and expose its continuation. -/
public theorem composite_eraseIndex_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) (herase : d.erasable = true)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .index R d, Z :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], Z, beta⟩⟩ := by
  exact ⟨.eraseIndex R d, herase, alpha, Z, beta, rfl, rfl⟩

/-- Close a completed pop frame and reactivate its saved continuation. -/
public theorem composite_returnFrame_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta gamma : List (WorkSym g)) (hZ : Z ≠ WorkSym.dollar)
    (hfree : DollarFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩⟩ := by
  exact ⟨.returnFrame, alpha, Z, beta, gamma, hZ, hfree, rfl, rfl⟩

/-! ## Singleton visible-stack layouts

The first, unbounded, completeness runner uses one compressed token for every inherited flag
which is actually consumed.  Compression is only needed later for the linear accounting.  A
layout records the index-free (but possibly `close`-containing) gaps between those singleton
tokens.  The additional dollar-free fact is exactly what is needed when a completed pop frame
returns through such a gap. -/

public theorem IndexFree.append {g : IndexedGrammar T}
    {xs ys : List (WorkSym g)} (hxs : IndexFree xs) (hys : IndexFree ys) :
    IndexFree (xs ++ ys) := by
  intro R d hm
  simp only [List.mem_append] at hm
  exact hm.elim (hxs R d) (hys R d)

public theorem DollarFree.append {g : IndexedGrammar T}
    {xs ys : List (WorkSym g)} (hxs : DollarFree xs) (hys : DollarFree ys) :
    DollarFree (xs ++ ys) := by
  intro hm
  simp only [List.mem_append] at hm
  exact hm.elim hxs hys

public inductive SingletonLayout (g : IndexedGrammar T) [Fintype g.nt] :
    List g.flag → List (WorkSym g) → List (WorkSym g) → Prop where
  | nil (tail : List (WorkSym g)) : SingletonLayout g [] tail tail
  | cons {f : g.flag} {flags : List g.flag}
      {beta tail tail' : List (WorkSym g)} {d : IndexMark}
      (indexFree : IndexFree beta) (dollarFree : DollarFree beta)
      (later : flags ≠ [] → d.later = true)
      (rest : SingletonLayout g flags tail tail') :
      SingletonLayout g (f :: flags)
        (beta ++ WorkSym.index (cflagBase g f) d :: tail)
        (beta ++ WorkSym.index (cflagBase g f) d.markUsed :: tail')

namespace SingletonLayout

/-- Marking an already used index is idempotent. -/
@[simp] public theorem IndexMark.markUsed_idem (d : IndexMark) :
    d.markUsed.markUsed = d.markUsed := by
  cases d <;> rfl

@[simp] public theorem IndexMark.markUsed_later (d : IndexMark) :
    d.markUsed.later = d.later := by
  cases d <;> rfl

/-- Once all selected tokens have been used, selecting them again leaves the physical word
unchanged. -/
public theorem idempotent {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) :
    SingletonLayout g flags used used := by
  induction layout with
  | nil tail => exact .nil tail
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      simpa using SingletonLayout.cons (f := f) (d := d.markUsed)
        hindex hdollar (fun hne => by
          simpa using hlater hne) ih

/-- Ordinary control symbols may be inserted before the first selected token.  In particular,
this is how a pending binary sibling or a crossed `close` is included in a pop gap. -/
public theorem prepend {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (pref : List (WorkSym g)) (hindex : IndexFree pref)
    (hdollar : DollarFree pref) (layout : SingletonLayout g flags word used) :
    SingletonLayout g flags (pref ++ word) (pref ++ used) := by
  induction layout with
  | nil tail => exact .nil (pref ++ tail)
  | @cons f flags beta tail tail' d hbetaIndex hbetaDollar hlater rest _ih =>
      simpa [List.append_assoc] using SingletonLayout.cons (f := f) (d := d)
        (hindex.append hbetaIndex) (hdollar.append hbetaDollar) hlater rest

/-- Restrict a layout to its first `n` selected flags.  The remaining physical tokens become
part of the arbitrary unselected tail. -/
public theorem splitTake {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (n : ℕ) (layout : SingletonLayout g flags word used) :
    ∃ middle,
      SingletonLayout g (flags.take n) word middle ∧
        SingletonLayout g flags middle used := by
  induction layout generalizing n with
  | nil tail => exact ⟨tail, by simpa using SingletonLayout.nil (g := g) tail,
      SingletonLayout.nil (g := g) tail⟩
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      cases n with
      | zero => exact ⟨_, .nil _, SingletonLayout.cons hindex hdollar hlater rest⟩
      | succ n =>
          rcases ih n with ⟨middle, hprefix, hremain⟩
          let next := beta ++ WorkSym.index (cflagBase g f) d.markUsed :: middle
          refine ⟨next, ?_, ?_⟩
          · exact SingletonLayout.cons (f := f) (d := d) hindex hdollar
              (fun hne => hlater (by
                intro hnil
                subst flags
                simp at hne)) hprefix
          · simpa [next] using SingletonLayout.cons (f := f)
              (d := d.markUsed) hindex hdollar
              (fun hne => by
                simpa using hlater hne) hremain

/-- Selecting the whole visible prefix reaches the all-used endpoint and leaves an idempotent
layout there. -/
public theorem splitAll {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) :
    SingletonLayout g (flags.take flags.length) word used ∧
      SingletonLayout g flags used used := by
  simpa using And.intro layout layout.idempotent

/-- Any prefix of an all-used layout is itself an identity layout.  This is used when one binary
child has already consumed the whole visible prefix and the other child consumes only part. -/
public theorem idempotentTake {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (n : ℕ) (layout : SingletonLayout g flags word used) :
    SingletonLayout g (flags.take n) used used := by
  induction layout generalizing n with
  | nil tail => simpa using SingletonLayout.nil (g := g) tail
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      cases n with
      | zero => exact .nil _
      | succ n =>
          simpa using SingletonLayout.cons (f := f) (d := d.markUsed)
            hindex hdollar (fun hne => by
              simpa using hlater (by
                intro hnil
                subst flags
                simp at hne)) (ih n)

end SingletonLayout

/-! ### Maximal consumed prefixes -/

/-- Before a known unused boundary, consumption consists of an initial segment. -/
public theorem NFParse.exists_consumedPrefix
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (n : ℕ) (hboundary : ¬ p.ConsumesAt n) :
    ∃ m ≤ n, (∀ k < m, p.ConsumesAt k) ∧ ¬ p.ConsumesAt m := by
  classical
  have hexists : ∃ k : ℕ, ¬ p.ConsumesAt k := ⟨n, hboundary⟩
  let m := Nat.find hexists
  refine ⟨m, Nat.find_min' hexists hboundary, ?_, Nat.find_spec hexists⟩
  intro k hk
  by_contra hnot
  exact Nat.find_min hexists hk hnot


end Aho
end IndexedGrammar
