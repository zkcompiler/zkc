module

public import ZkcSecurity.Families.Sumcheck.Contract
public import Zkc.Obligations.FrameComposition

@[expose] public section

/-! The existing Sumcheck residual mathematics with an abstract escape policy.
This permits a source policy quantified over actual routed distributions.
Message fixation, degree and false-round preservation are the family laws;
the structural induction is independent of the message representation. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.SumcheckResidual
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Families.Sumcheck
variable {F : Type} [Field F] [DecidableEq F]
  {I : PIR.Signature} {Context : Type} {State : Nat → Type}
  {message : Message F} {reference : Reference F}
  {program : Program I Context State message} {E P : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}

theorem yields_true {B : Type} (process : PIR.Process I B) :
    PIR.Yields (fun _ => True) process := by
  induction process with
  | done => trivial
  | halt => trivial
  | call _ _ ih => exact ih

noncomputable def remaining
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (queries : QueryInterface program absorb)
    (empty : ∀ history event, escape history event (fun _ => False))
    (sampling : ∀ {n} (context : Context) (state : State (n + 1)), representation.Allowed state →
      ∀ m history (p q : Polynomial F), p ≠ q →
      p.natDegree ≤ messageDegree → q.natDegree ≤ referenceDegree →
      escape history (queries.event context state m)
        (fun raw => p.eval (queries.challenge context state m raw) =
          q.eval (queries.challenge context state m raw)))
    {n : Nat} (count : Nat) (context : Context) (state : State (n + count))
    (history : List E) (wrong : representation.No state) :
    Derivation absorb escape (fun _ result => representation.No result) history
      (program.remaining count context state) := by
  induction count generalizing history with
  | zero => exact .done wrong
  | succ count ih =>
    unfold Program.remaining
    apply (Derivation.ofYields empty (yields_true (program.receive context state)) history).bind
    intro reached decoded _
    cases decoded with
    | none => exact .halt .refused
    | some m =>
      apply Derivation.guard
      intro checked
      refine .query (queries.absorbed context state m) _
        (sampling context state wrong.1 m reached _ _
          (checked_polynomial_ne referenceLaws messageLaws _ wrong.1 _ wrong.2 m checked)
          (messageLaws.degree_le m) (referenceLaws.degree_le _ wrong.1)) ?_
      intro raw reply decoded outside
      apply (Derivation.ofYields empty (yields_true
        (program.deliver context state m (program.challenge context state m reply))) _).bind
      intro final _ _
      apply ih _ _
      have falsehood := false_round referenceLaws messageLaws (representation.state state)
        wrong.1 m (queries.challenge context state m raw) outside
      refine ⟨representation.advance_allowed referenceLaws context state wrong.1 m _, ?_⟩
      rw [representation.claim, representation.advance, queries.decoded context state m raw reply decoded]
      exact falsehood.1

end ZkcSecurity.Source.SumcheckResidual
