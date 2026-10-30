module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilySelections
public meta import ZkcTools.StructuredSource.PropertyInstallation

@[expose] public section

/-! Two admitted clients of the same family installation, a pending body law,
with exact source identity. These checks do not rebuild GKR's
admission or its constructed participant connection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.SourceTemplateInstallation
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcSecurity.Realizations.Sumcheck ZkcExamples.Structured SumcheckSourceSelections

variable {program : Structured.Program} (installation : SourceFamily.Installation program)
  (model : DomainModel)

/-- The installer exposes the body equation when no selected law closes it.
The supplied function is applied explicitly after installation; it is not a
whole-invocation equality or an assumed property of a compiled participant. -/
theorem pending_body (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (args : Binders model SourceFamily.producerPattern.scope)
    (others : Values (Component model.Value) SourceFamily.producerPattern.absentTypes)
    (reference : PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs))
    (bodyLaw : Unit → SourceFamily.producerReduction installation model ctx args = reference) :
    invokeProtocol (Occurrence.table model program.payload)
      (SourceFamily.reductionSignature installation.reductionName) ctx (ctx.roles 0)
      (SourceFamily.producerPattern.fill model args others) =
      reference.bind fun out => .done (staticMask 0 out
        (SourceFamily.reductionSignature installation.reductionName).outputScopes
        (Operands.identity SumcheckVerifierBodies.reduceOutputs)) := by
  install_source_template installation.reduction using_pattern SourceFamily.producerPattern
  exact bodyLaw ()

/-- SmallSumcheck (bound two) and TwoSums (bound four) install the exact
selected source body through the same tactic and family presentation. -/
theorem selected_producer (selection : Selection) (model : DomainModel)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (args : Binders model SourceFamily.producerPattern.scope)
    (others : Values (Component model.Value) SourceFamily.producerPattern.absentTypes) :
    invokeProtocol (Occurrence.table model (source selection).payload)
      (SourceFamily.reductionSignature (SourceFamilySelections.installed selection).reductionName)
      ctx (ctx.roles 0) (SourceFamily.producerPattern.fill model args others) =
      (SourceFamily.producerReduction (SourceFamilySelections.installed selection) model ctx args).bind
        fun out => .done (staticMask 0 out
          (SourceFamily.reductionSignature (SourceFamilySelections.installed selection).reductionName).outputScopes
          (Operands.identity SumcheckVerifierBodies.reduceOutputs)) := by
  install_source_template (SourceFamilySelections.installed selection).reduction
    using_pattern SourceFamily.producerPattern
  rfl

#check selected_producer .small
#check selected_producer .twoSums
#print axioms pending_body
#print axioms selected_producer
end TestsSecurity.SourceTemplateInstallation
