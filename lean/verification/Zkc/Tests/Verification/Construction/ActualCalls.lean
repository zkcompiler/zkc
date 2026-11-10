module

public import Zkc.Tests.Verification.Construction.TwiceSource
public meta import Zkc.Tools.Program.Companions.Goals

/-! One mathematical helper law at two real calls with different ordered operands.
There is no companion-authored body, register selection or closure traversal. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Source.Structured ProtocolProof Std.WP
namespace ActualSourceConstruction.Twice

bind_source_helper difference from actual named "s12h61637475616c5f63616c6c7310h646966666572656e6365"
bind_source_protocol twice from actual named "s12h61637475616c5f63616c6c735h5477696365"

variable (model : DomainModel) {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]

companion_goal DifferenceLaw in
/-- The mathematical computation is independent of a caller's frame and service state. -/
@[spec high] theorem difference_law (observations : SiteObservations I)
    (table : Evaluation.MeaningsOn model.toCarriers I)
    (arguments : Values model.Value difference.signature.inputs)
    (post : Values model.Value difference.signature.outputs → Pred) (stopped : EPred) :
    ⦃post (.singleton (arguments.get .here - arguments.get (.there .here)))⦄
      difference.body.denote (Evaluation.meaningOn model observations table) arguments.get
      ⦃post; stopped⦄ := by
  construct_region

/-- The full actual participant returns both ordered differences under any operation model. -/
theorem participant_law [WPMonad (Process (participantInterfaceOn model.toCarriers)) Pred EPred]
    (x y : model.Field "bls12-381.fr")
    (post : Values (Component model.Value) twice.signature.outputs → Pred) (stopped : EPred) :
    ⦃post (.cons (some (x - y)) (.cons (some (y - x)) .nil))⦄
      actual.program.participantOn model 0 (.cons (some x) (.cons (some y) .nil))
      ⦃post; stopped⦄ := by
  construct_region

#print axioms participant_law
end ActualSourceConstruction.Twice
