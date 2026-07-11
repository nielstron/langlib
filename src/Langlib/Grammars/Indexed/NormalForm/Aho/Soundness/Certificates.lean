module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Control

@[expose]
public section

/-!
# Certificate soundness for Aho's machine

Every certified composite step has its stated grammar or input-consumption effect.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace ControlDenotation

open BlockDenotation

/-! ## Every finite certificate is denotationally sound -/

public def StepEffect (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (c c' : Config g) (form form' : List g.ISym) : Prop :=
  (c'.inputPos = c.inputPos ∧ g.Derives form form') ∨
    ∃ a, form = ISym.terminal a :: form' ∧
      input[c.inputPos]? = some a ∧ c'.inputPos = c.inputPos + 1

public theorem certStep_preserves_represents
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) {c c' : Config g} {form : List g.ISym}
    (hstep : CertStep g input cert c c')
    (hrep : Config.Represents c form) :
    ∃ form', Config.Represents c' form' ∧ StepEffect g input c c' form form' := by
  change ExecRep g (normalizeCursor c.work) form at hrep
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainBinary haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainTerminal A a =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainTerminal haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainPushSkip A B f =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainPushSkip haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainPushUse A B f =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainPushUse haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym, normalizeIndexMark] using hrep'
          · rw [hc']
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryBoth haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryLeft haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | liveBinaryRight A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryRight haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | livePushFresh A B f =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.livePushFresh haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym, normalizeIndexMark] using hrep'
      · rw [hc']
  | livePushCompress A B f R d =>
      rcases hstep with ⟨haug, _hne, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          rcases hrep.invertLive with
            ⟨actual, stack, tailForm, hform, rightRep, decorates, tailExec⟩
          exact False.elim (tailExec.right_ne_nil_of_index_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.livePushCompress haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym] using hrep'
          · rw [hc']
  | popPlain R d A B =>
      rcases hstep with ⟨hedge, hframed | herase⟩
      · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append,
          List.map_cons, normalizeWorkSym] at hrep
        have hfree' : IndexFree (beta.map normalizeWorkSym) :=
          (indexFree_map_normalizeWorkSym beta).2 hfree
        rcases hrep.popPlain hfree' hedge with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, List.nil_append, List.append_nil,
            List.singleton_append, List.cons_append, List.append_assoc,
            normalizeWorkSym, normalizeIndexMark,
            normalizeIndexMark_markUsed, IndexMark.later_markUsed] using hrep'
        · rw [hc']
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append,
          List.map_cons, normalizeWorkSym] at hrep
        rcases hrep.popPlainErase hedge with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] using hrep'
        · rw [hc']
  | popLive R d A B =>
      rcases hstep with ⟨hedge, hlater, hframed | herase⟩
      · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append,
          List.map_cons, normalizeWorkSym] at hrep
        have hfree' : IndexFree (beta.map normalizeWorkSym) :=
          (indexFree_map_normalizeWorkSym beta).2 hfree
        have hlater' : (normalizeIndexMark d).later = true := by simpa using hlater
        rcases hrep.popLive hfree' hedge hlater' with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, List.nil_append, List.append_nil,
            List.singleton_append, List.cons_append, List.append_assoc,
            normalizeWorkSym, normalizeIndexMark,
            normalizeIndexMark_markUsed, IndexMark.later_markUsed] using hrep'
        · rw [hc']
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append,
          List.map_cons, normalizeWorkSym] at hrep
        have hlater' : (normalizeIndexMark d).later = true := by simpa using hlater
        rcases hrep.popLiveErase hedge hlater' with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] using hrep'
        · rw [hc']
  | matchTerminal a =>
      rcases hstep with ⟨hinput, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.matchTerminal with ⟨restForm, hform, hrep'⟩
      refine ⟨restForm, ?_, Or.inr ⟨a, hform, hinput, ?_⟩⟩
      · change ExecRep g (normalizeCursor c'.work) restForm
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']
  | eraseIndex R d =>
      rcases hstep with ⟨_herase, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      have hrep' := hrep.eraseIndex
      refine ⟨form, ?_, Or.inl ⟨?_, deri_self g form⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, hZ, hfree, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append,
        List.map_cons, normalizeWorkSym] at hrep
      have hZ' : normalizeWorkSym Z ≠ WorkSym.dollar :=
        (normalizeWorkSym_ne_dollar_iff Z).2 hZ
      have hfree' : DollarFree (beta.map normalizeWorkSym) :=
        (dollarFree_map_normalizeWorkSym beta).2 hfree
      have hrep' := hrep.returnFrameSound hZ' hfree'
      refine ⟨form, ?_, Or.inl ⟨?_, deri_self g form⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']

end ControlDenotation
end Aho
end IndexedGrammar
