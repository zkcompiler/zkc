module

public import Zkc.Tests.Verification.Construction.ReplaceSource

/-! The actual finite loop uses one mathematical invariant and the common structural rules.
The zero-trip case keeps the input; every positive count returns the captured replacement. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Source.Structured ProtocolProof Std.WP
namespace ActualSourceConstruction.Replace

bind_source_helper replaceValue from actual named "s14h73636f7065645f636f6e74726f6c7h7265706c616365"
bind_source_protocol replaceProtocol from actual named "s14h73636f7065645f636f6e74726f6c7h5265706c616365"

variable (model : DomainModel) {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]

@[spec high] theorem replace_law
    (table : Evaluation.MeaningsOn model.toCarriers I)
    (arguments : Values model.Value replaceValue.signature.inputs)
    (post : Values model.Value replaceValue.signature.outputs → Pred) (stopped : EPred) :
    ⦃post (.singleton (if arguments.get (.there (.there .here)) = 0 then
      arguments.get .here else arguments.get (.there .here)))⦄
      replaceValue.body.denote (Evaluation.meaningOn model (.silent I) table) arguments.get
      ⦃post; stopped⦄ := by
  construct_region with_invariants [fun remaining state =>
    post (.singleton (if remaining.isEmpty then state.get .here else arguments.get (.there .here)))]
  all_goals simp
  all_goals exact Lean.Order.PartialOrder.rel_refl

/-- The complete participant, for arbitrary runtime counts including zero. -/
theorem participant_law [WPMonad (Process (participantInterfaceOn model.toCarriers)) Pred EPred]
    (x y : model.Field "bls12-381.fr") (count : Nat)
    (post : Values (Component model.Value) replaceProtocol.signature.outputs → Pred)
    (stopped : EPred) :
    ⦃post (.singleton (some (if count = 0 then x else y)))⦄
      actual.program.participantOn model 0
        (.cons (some x) (.cons (some y) (.cons (some count) .nil)))
      ⦃post; stopped⦄ := by
  construct_region

#print axioms participant_law
end ActualSourceConstruction.Replace
