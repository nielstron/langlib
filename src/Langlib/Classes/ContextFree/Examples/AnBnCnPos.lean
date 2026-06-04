module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AnBnCnPos
import Langlib.Examples.AnBnCn
import Langlib.Classes.ContextFree.Examples.AnBnCn
import Langlib.Classes.ContextFree.Closure.Union
import Langlib.Classes.ContextFree.Closure.Homomorphism
@[expose]
public section

/-! # `{aⁿbⁿcⁿ | n ≥ 1}` is not context-free

The positive witness `lang_eq_eq_pos` differs from `lang_eq_eq = {aⁿbⁿcⁿ}` only by the
empty word, so if it were context-free then `lang_eq_eq = lang_eq_eq_pos ∪ {ε}` would be
too — contradicting `notCF_lang_eq_eq`.
-/

private lemma lang_eq_eq_eq_pos_union_epsilon :
    lang_eq_eq = lang_eq_eq_pos + ({[]} : Language (Fin 3)) := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero =>
        exact Or.inr rfl
    | succ n =>
        left
        exact ⟨n, rfl⟩
  · intro hw
    rw [Language.add_def] at hw
    rcases hw with hw | hw
    · obtain ⟨n, rfl⟩ := hw
      exact ⟨n + 1, rfl⟩
    · rw [Set.mem_singleton_iff] at hw
      subst w
      exact ⟨0, by simp⟩

public theorem notCF_lang_eq_eq_pos : ¬ is_CF lang_eq_eq_pos := by
  intro hpos
  apply notCF_lang_eq_eq
  rw [lang_eq_eq_eq_pos_union_epsilon]
  exact CF_of_CF_u_CF lang_eq_eq_pos ({[]} : Language (Fin 3))
    ⟨hpos, is_CF_singleton []⟩

end
