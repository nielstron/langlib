import Mathlib

/-!
# DFA membership is computable

We show that the language accepted by a DFA is a computable predicate,
in the sense of Mathlib's computability theory (partial recursive functions / Turing machines).

The key idea: `DFA.eval` is `List.foldl M.step M.start`, which is primitive recursive
when `M.step` is primitive recursive (via `Primrec.list_foldl`). Membership in `M.accepts`
then reduces to applying a decidable/computable predicate to the result.

## Main results

* `DFA.primrec₂_evalFrom` — `DFA.evalFrom` is primitive recursive when `M.step` is.
* `DFA.primrec_eval` — `DFA.eval` is primitive recursive when `M.step` is.
* `DFA.computablePred_accepts` — membership in `M.accepts` is a computable predicate.
-/

open Computability

variable {α : Type} {σ : Type}

/-- `DFA.evalFrom` is primitive recursive when the step function is. -/
theorem DFA.primrec₂_evalFrom [Primcodable α] [Primcodable σ]
    (M : DFA α σ) (h_step : Primrec₂ M.step) :
    Primrec₂ M.evalFrom := by
  unfold DFA.evalFrom
  show Primrec (fun (p : σ × List α) => List.foldl M.step p.1 p.2)
  have h2 : Primrec₂ (fun (_ : σ × List α) (sb : σ × α) => M.step sb.1 sb.2) :=
    h_step.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)
  exact Primrec.list_foldl Primrec.snd Primrec.fst h2

/-- `DFA.eval` is primitive recursive when the step function is. -/
theorem DFA.primrec_eval [Primcodable α] [Primcodable σ]
    (M : DFA α σ) (h_step : Primrec₂ M.step) :
    Primrec M.eval :=
  (M.primrec₂_evalFrom h_step).comp (Primrec.const M.start) Primrec.id

/-- `DFA.eval` is computable when the step function is. -/
theorem DFA.computable_eval [Primcodable α] [Primcodable σ]
    (M : DFA α σ) (h_step : Primrec₂ M.step) :
    Computable M.eval :=
  (M.primrec_eval h_step).to_comp

/-- Membership in a DFA's accepted language is a computable predicate,
provided the step function is primitive recursive and membership in the accept set
is decidable and computable. -/
theorem DFA.computablePred_accepts [Primcodable α] [Primcodable σ]
    (M : DFA α σ) (h_step : Primrec₂ M.step)
    (h_accept_dec : DecidablePred (· ∈ M.accept))
    (h_accept : @Computable _ _ _ _ (fun s => @decide (s ∈ M.accept) (h_accept_dec s))) :
    ComputablePred (· ∈ M.accepts) := by
  refine ⟨fun x => h_accept_dec (M.eval x), ?_⟩
  show Computable (fun x => @decide (M.eval x ∈ M.accept) (h_accept_dec (M.eval x)))
  exact h_accept.comp (M.computable_eval h_step)
