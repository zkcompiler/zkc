import Examples.OpeningReduction.Openings
import Zkc.Realization.Acceptance

/-! Exact output realization for the actual round source and opening consumer.

The witness is a residual of the executed prefix. Constraints bind the delivered
point, product check and complete ordered bundle. They do not assert that the
reported openings are true. A following consumer must establish that separately.
This is a logical relation target, not an arithmetic circuit or PCS proof.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Acceptance

open PIR Openings

structure Input (Id F S : Type) where
  objects : Objects Id
  rounds : Nat
  claim : F
  prover : S
  coins : List F

variable {Id F S : Type} [CommRing F] [DecidableEq F]

def produces (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (input : Input Id F S) (output : Bundle Id F input.rounds) : Prop :=
  (Openings.run send react report input.objects input.rounds input.claim
    input.prover input.coins).outcome = .returned output

def constraints (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (input : Input Id F S) (output : Bundle Id F input.rounds) (acc : Source.Accumulator F) : Prop :=
  let rounds := Execution.run send react input.rounds input.claim input.prover input.coins
  let values := (report rounds.state.1 acc).1
  rounds.outcome = .returned acc ∧
    acc.challenges.length = input.rounds ∧
    values.first * values.second * values.third = acc.claim ∧
    bundle input.objects (Zkc.Polynomial.coordinates input.rounds acc.challenges) values = output

theorem realization (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S) :
    Zkc.Realization.Acceptance (produces (Id := Id) send react report)
      (constraints send react report) where
  sound input output acc valid := by
    obtain ⟨returned, closed⟩ := valid
    have checked := (close_returned input.objects acc _ output).mpr closed
    simpa only [produces, Openings.run, PIR.Execution.follow, returned] using checked
  complete input output returned := by
    obtain ⟨acc, returnedRounds, closed⟩ := run_returned send react report input.objects
      input.rounds input.claim input.prover input.coins output returned
    exact ⟨acc, returnedRounds, (close_returned input.objects acc _ output).mp closed⟩

/-- The terminal obligation is on the same returned bundle, including all
object identities, coordinates and values; it cannot be hidden independently. -/
theorem followed_by_openings (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (input : Input Id F S) (env : Id → Table F input.rounds) :
    (∃ output acc, constraints send react report input output acc ∧ AllHold env output) ↔
      ∃ output, produces send react report input output ∧ AllHold env output := by
  constructor
  · rintro ⟨output, acc, valid, holds⟩
    exact ⟨output, (realization send react report).sound input output acc valid, holds⟩
  · rintro ⟨output, returned, holds⟩
    obtain ⟨acc, valid⟩ := (realization send react report).complete input output returned
    exact ⟨output, acc, valid, holds⟩

end Examples.OpeningReduction.Acceptance
