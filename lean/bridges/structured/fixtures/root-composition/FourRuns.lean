module

public import TestsSecurity.RootComposition.FourSource

@[expose] public section

/-! Concrete executions supplement the general all-input source equations.
They are not a root Pair theorem or endpoint completeness receipt. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.RootComposition.Four.Source
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck

def honestProducerArguments : Binders (ringModel Rat Rat)
    (Zkc.Source.Structured.NormalizedRoot.pattern program 0).scope :=
  .cons (some [0,0]) (.cons (some [0,0]) (.cons (some [0,0]) (.cons (some [0,0])
    (.cons (some 1) .nil))))

def honestValidatorArguments : Binders (ringModel Rat Rat)
    (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope :=
  .cons (some [0,0]) (.cons (some [0,0]) (.cons (some [0,0]) (.cons (some [0,0])
    (.cons (some 0) (.cons (some 0) (.cons (some 0) (.cons (some 0)
      (.cons (some 1) (.cons (some 0) .nil)))))))))

/-- All four producer calls really send both values and consume a challenge. -/
theorem honest_producer_four_calls :
    let run := (Occurrence.participant (ringModel Rat Rat) program 0
      (Zkc.Source.Structured.NormalizedRoot.inputs (ringModel Rat Rat) honestProducerArguments)).run zeroReplies ()
    run.events.length = 12 ∧ run.outcome = .returned (.cons none .nil) := by
  rw [SourceFamily.producer_equation installation _ producer]
  constructor <;> kernel_rfl

/-- The balanced conjunction accepts the honest zero-table example. -/
theorem honest_validator_four_calls :
    let run := (Occurrence.participant (ringModel Rat Rat) program 1
      (Zkc.Source.Structured.NormalizedRoot.inputs (ringModel Rat Rat) honestValidatorArguments)).run zeroReplies ()
    run.events.length = 16 ∧ run.outcome = .returned (.cons (some true) .nil) := by
  rw [SourceFamily.validator_equation installation _ validator]
  constructor <;> kernel_rfl

#print axioms malformed_four_calls
#print axioms honest_producer_four_calls
#print axioms honest_validator_four_calls
end TestsSecurity.RootComposition.Four.Source
