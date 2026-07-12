module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Denotation.Control

@[expose]
public section

/-!
# Control-effect soundness for Aho's machine

Grammar effects of local, close-crossing, and structural control moves.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace ControlDenotation

open BlockDenotation

/-- Read a delimiter-free suffix split uniquely from the right. -/
private theorem append_delimiter_unique
    {α : Type} [DecidableEq α] {delimiter : α}
    {left₁ left₂ right₁ right₂ : List α}
    (hfree₁ : delimiter ∉ right₁) (hfree₂ : delimiter ∉ right₂)
    (heq : left₁ ++ delimiter :: right₁ = left₂ ++ delimiter :: right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hrev : right₁.reverse ++ delimiter :: left₁.reverse =
      right₂.reverse ++ delimiter :: left₂.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse heq
  have first_unique : ∀ {xs ys p q : List α},
      delimiter ∉ xs → delimiter ∉ ys →
      xs ++ delimiter :: p = ys ++ delimiter :: q → xs = ys ∧ p = q := by
    intro xs
    induction xs with
    | nil =>
        intro ys p q hxs hys heq
        cases ys with
        | nil => simpa using heq
        | cons y ys =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            exact False.elim (hys (by simp [heq.1]))
    | cons x xs ih =>
        intro ys p q hxs hys heq
        cases ys with
        | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
            exact False.elim (hxs (by simp [heq.1]))
        | cons y ys =>
            simp only [List.cons_append, List.cons.injEq] at heq
            have hxs' : delimiter ∉ xs :=
              fun hm => hxs (List.mem_cons_of_mem x hm)
            have hys' : delimiter ∉ ys :=
              fun hm => hys (List.mem_cons_of_mem y hm)
            rcases ih hxs' hys' heq.2 with
              ⟨hxy, hpq⟩
            exact ⟨by simp [heq.1, hxy], hpq⟩
  rcases first_unique (by simpa using hfree₁) (by simpa using hfree₂) hrev with
    ⟨hright, hleft⟩
  exact ⟨by simpa using congrArg List.reverse hleft,
    by simpa using congrArg List.reverse hright⟩

/-! ## Local grammar effects in the execution-order denotation -/

public theorem ExecRep.plainBinary
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.plain B, WorkSym.plain C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B actual (RightRep.plain C rightRep) decorates
        (ExecRep.plain C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.plainTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A : g.nt} {a : T} (haug : AugTerminal g A a)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g ⟨left, WorkSym.terminal a, next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.terminal a tail, ?_⟩
      simpa using deri_with_suffix _ (augTerminal_derives haug actual)

public theorem ExecRep.plainPushSkip
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g ⟨left, WorkSym.plain B, next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B (f :: actual) rightRep
        (decorates.pushHidden f) tail, ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.plainPushUse
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagBase g f) .firstPending :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      let block : VisibleBlock g := ⟨[f], false⟩
      have indexedRep : RightRep g
          (WorkSym.index (cflagBase g f) .firstPending :: next :: right)
          (block :: _) :=
        RightRep.index (cflagBase g f) .firstPending [f]
          (CFlag.Denotes.base f) rightRep
      refine ⟨_, ExecRep.live B (f :: actual) indexedRep
        (decorates.pushFirst f) (ExecRep.index _ _ tail), ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.liveBinaryBoth
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B, WorkSym.live C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.live B actual (RightRep.live C rightRep) decorates
        (ExecRep.live C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.liveBinaryLeft
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B, WorkSym.plain C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.live B actual (RightRep.plain C rightRep) decorates
        (ExecRep.plain C actual rightRep decorates.toDecorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.liveBinaryRight
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.plain B, WorkSym.live C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B actual (RightRep.live C rightRep)
        decorates.toDecorates (ExecRep.live C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.livePushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagBase g f) .laterPending :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      have indexedRep := RightRep.index (cflagBase g f) .laterPending [f]
        (CFlag.Denotes.base f) rightRep
      refine ⟨_, ExecRep.live B (f :: actual) indexedRep
        (decorates.pushLater f) (ExecRep.index _ _ tail), ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.livePushCompress
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} {R : CFlag g} {d : IndexMark}
    (haug : AugPush g A B f)
    (h : ExecRep g
      ⟨left, WorkSym.live A, WorkSym.index R d :: next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagComp g (cflagBase g f) R) d :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      cases rightRep with
      | index _ _ flags denotes restRep =>
          cases tail with
          | index _ _ restExec =>
              have denotes' : CFlag.Denotes g (f :: flags)
                  (cflagComp g (cflagBase g f) R) := by
                simpa using CFlag.Denotes.comp (CFlag.Denotes.base f) denotes
              have indexedRep := RightRep.index
                (cflagComp g (cflagBase g f) R) d (f :: flags) denotes' restRep
              refine ⟨_, ExecRep.live B (f :: actual) indexedRep
                (decorates.pushCompress f) (ExecRep.index _ _ restExec), ?_⟩
              simpa using deri_with_suffix _ (augPush_derives haug actual)

/-! ## Close-crossing pop effects -/

public theorem ExecRep.invertLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A : g.nt}
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ actual stack tailForm,
      form = ISym.indexed A actual :: tailForm ∧
        RightRep g (next :: right) stack ∧
        LiveDecorates stack actual ∧
        ExecRep g ⟨left, next, right⟩ tailForm := by
  cases h with
  | live _ actual rightRep decorates tail =>
      exact ⟨actual, _, _, rfl, rightRep, decorates, tail⟩

public theorem ExecRep.popPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        beta ++ WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar] ++ beta ++
            [WorkSym.index R d, WorkSym.dollar],
          WorkSym.plain B, WorkSym.close :: gamma⟩ form' ∧
      g.Derives form form' := by
  cases beta with
  | nil =>
      simp only [List.nil_append, List.append_nil] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      cases rightRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
          subst actual
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha) (beta := [])
                (gamma := gamma) (by simp [DollarFree]) tailExec)
          refine ⟨_, ExecRep.plain B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)
  | cons z zs =>
      simp only [List.cons_append] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      rcases rightRep_append (xs := z :: zs)
        (ys := WorkSym.index R d :: gamma) rightRep with
        ⟨middle, selectedRep, betaRep⟩
      have hstack := betaRep.stack_eq_of_indexFree hfree
      subst middle
      cases selectedRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
          subst actual
          have hfreeTail : DollarFree (zs ++ [WorkSym.index R d]) := by
            intro hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact betaRep.dollarFree (List.mem_cons_of_mem z hm)
            · cases hm
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], z,
                (zs ++ [WorkSym.index R d]) ++ gamma⟩ tailForm := by
            simpa [List.append_assoc] using tailExec
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++ z :: zs ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
                simpa [List.append_assoc] using
                  (ExecRep.returnFrame (alpha := alpha)
                    (beta := zs ++ [WorkSym.index R d])
                    (gamma := gamma) hfreeTail tailExec')
          refine ⟨_, ExecRep.plain B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

public theorem ExecRep.popLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true) (hlater : d.later = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        beta ++ WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar] ++ beta ++
            [WorkSym.index R d, WorkSym.dollar],
          WorkSym.live B, WorkSym.close :: gamma⟩ form' ∧
      g.Derives form form' := by
  cases beta with
  | nil =>
      simp only [List.nil_append, List.append_nil] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      cases rightRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
          subst actual
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha) (beta := [])
                (gamma := gamma) (by simp [DollarFree]) tailExec)
          refine ⟨_, ExecRep.live B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

  | cons z zs =>
      simp only [List.cons_append] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      rcases rightRep_append (xs := z :: zs)
        (ys := WorkSym.index R d :: gamma) rightRep with
        ⟨middle, selectedRep, betaRep⟩
      have hstack := betaRep.stack_eq_of_indexFree hfree
      subst middle
      cases selectedRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
          subst actual
          have hfreeTail : DollarFree (zs ++ [WorkSym.index R d]) := by
            intro hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact betaRep.dollarFree (List.mem_cons_of_mem z hm)
            · cases hm
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], z,
                (zs ++ [WorkSym.index R d]) ++ gamma⟩ tailForm := by
            simpa [List.append_assoc] using tailExec
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++ z :: zs ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha)
                (beta := zs ++ [WorkSym.index R d])
                (gamma := gamma) hfreeTail tailExec')
          refine ⟨_, ExecRep.live B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

/-! ## Structural execution effects -/

public theorem ExecRep.matchTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {a : T}
    (h : ExecRep g ⟨left, WorkSym.terminal a, next :: right⟩ form) :
    ∃ restForm, form = ISym.terminal a :: restForm ∧
      ExecRep g ⟨left, next, right⟩ restForm := by
  cases h with
  | terminal _ tail => exact ⟨_, rfl, tail⟩

public theorem ExecRep.eraseIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : ExecRep g ⟨left, WorkSym.index R d, next :: right⟩ form) :
    ExecRep g ⟨left, next, right⟩ form := by
  cases h with
  | index _ _ tail => exact tail

/-- Generic inversion at a close focus. -/
public theorem ExecRep.invertClose
    {g : IndexedGrammar T} [Fintype g.nt]
    {left right : List (WorkSym g)} {form : List g.ISym}
    (h : ExecRep g ⟨left, WorkSym.close, right⟩ form) :
    ∃ alpha beta Z,
      DollarFree beta ∧
        left = alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar] ∧
        ExecRep g ⟨alpha ++ [WorkSym.dollar], Z, beta ++ right⟩ form := by
  cases h with
  | returnFrame hfree tail => exact ⟨_, _, _, hfree, rfl, tail⟩

public theorem ExecRep.focus_ne_dollar
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym}
    (h : ExecRep g cursor form) : cursor.focus ≠ WorkSym.dollar := by
  cases h <;> simp

public theorem ExecRep.right_ne_nil_of_plain_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym} {A : g.nt}
    (h : ExecRep g cursor form) (hfocus : cursor.focus = WorkSym.plain A) :
    cursor.right ≠ [] := by
  induction h <;> simp_all

public theorem ExecRep.right_ne_nil_of_index_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : ExecRep g cursor form) (hfocus : cursor.focus = WorkSym.index R d) :
    cursor.right ≠ [] := by
  induction h <;> simp_all

/-- Consume an adjacent compressed block and erase its representation immediately. Unlike the
framed pop, no saved index is needed because this block is owned exclusively by the active
task. -/
public theorem ExecRep.popPlainErase
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hedge : R A B = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, gamma⟩ form' ∧
      g.Derives form form' := by
  rcases h.invertLive with
    ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
  cases rightRep with
  | index _ _ flags denotes gammaRep =>
      rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
      subst actual
      have hgamma : gamma ≠ [] := tailExec.right_ne_nil_of_index_focus rfl
      cases gamma with
      | nil => exact False.elim (hgamma rfl)
      | cons next right =>
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], next, right⟩ tailForm :=
            tailExec.eraseIndex
          refine ⟨_, ExecRep.plain B rest gammaRep restDecorates tailExec', ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

/-- Live counterpart of `popPlainErase` for a lower represented stack that remains active. -/
public theorem ExecRep.popLiveErase
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hedge : R A B = true) (hlater : d.later = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar], WorkSym.live B, gamma⟩ form' ∧
      g.Derives form form' := by
  rcases h.invertLive with
    ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
  cases rightRep with
  | index _ _ flags denotes gammaRep =>
      rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
      subst actual
      have hgamma : gamma ≠ [] := tailExec.right_ne_nil_of_index_focus rfl
      cases gamma with
      | nil => exact False.elim (hgamma rfl)
      | cons next right =>
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], next, right⟩ tailForm :=
            tailExec.eraseIndex
          refine ⟨_, ExecRep.live B rest gammaRep restDecorates tailExec', ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

public theorem ExecRep.returnFrameSound
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {Z : WorkSym g}
    {form : List g.ISym}
    (hZ : Z ≠ WorkSym.dollar) (hfree : DollarFree beta)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
        WorkSym.close, gamma⟩ form) :
    ExecRep g ⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩ form := by
  rcases h.invertClose with
    ⟨alpha', beta', Z', hfree', hleft, tail⟩
  have hZ' : Z' ≠ WorkSym.dollar := tail.focus_ne_dollar
  have hsuffix : DollarFree (Z :: beta) := by
    intro hm
    simp only [List.mem_cons] at hm
    exact hm.elim (fun heq => hZ heq.symm) hfree
  have hsuffix' : DollarFree (Z' :: beta') := by
    intro hm
    simp only [List.mem_cons] at hm
    exact hm.elim (fun heq => hZ' heq.symm) hfree'
  have hwithoutLast :
      alpha ++ WorkSym.dollar :: Z :: beta =
        alpha' ++ WorkSym.dollar :: Z' :: beta' := by
    apply List.append_cancel_right (bs := [WorkSym.dollar])
    simpa [List.append_assoc] using hleft
  rcases append_delimiter_unique
      hsuffix hsuffix' hwithoutLast with ⟨halpha, hsaved⟩
  simp only [List.cons.injEq] at hsaved
  rcases hsaved with ⟨hZeq, hbeta⟩
  subst alpha'
  subst Z'
  subst beta'
  exact tail

end ControlDenotation
end Aho
end IndexedGrammar
