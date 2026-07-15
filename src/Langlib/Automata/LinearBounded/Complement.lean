module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.LBA

@[expose]
public section

/-!
# Linear-bounded automata are closed under positive complement

The marker-free `is_LBA_pos` model has no tape cells on the empty input, so its
complement operation is necessarily relative to the nonempty words.  Given an LBA,
we expose its finite configuration graph as a `CertifiedRowSystem`, apply the
inductive-counting complement construction there, and compile the resulting row
system back to an input-sized LBA.

The full complement theorem for context-sensitive languages, including the empty
word, is derived in `Classes/ContextSensitive/Closure/Complement.lean`.
-/

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The nonempty complement of an input-sized LBA language is again recognized by
an input-sized LBA.  Removing `{[]}` is unavoidable: every `is_LBA_pos` language
rejects the empty word. -/
public theorem is_LBA_pos_complement {L : Language T} (hL : is_LBA_pos L) :
    is_LBA_pos (Lᶜ \ ({[]} : Set (List T))) := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hL
  letI : Fintype Γ := hΓ
  letI : Fintype Λ := hΛ
  letI : DecidableEq Γ := hdΓ
  letI : DecidableEq Λ := hdΛ
  letI : Nonempty (LBA.RowCell T (Option (T ⊕ Γ)) Λ) :=
    ⟨LBA.RowCell.cfg none false M.initial⟩
  let S := LBA.certifiedRowSystem M (fun t : T => some (Sum.inl t))
  have hcomp := CertifiedRowSystem.is_LBA_pos_complement_rowReachLanguage S
  have hrows : S.rowReachLanguage =
      LBA.LanguageViaEmbed M (fun t : T => some (Sum.inl t)) := by
    exact LBA.certifiedRowSystem_rowReachLanguage M (fun t : T => some (Sum.inl t))
  rw [hrows, hM] at hcomp
  exact hcomp
