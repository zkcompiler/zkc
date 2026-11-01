module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs
public import Zkc.Source.Structured.NormalizedRoot
public import Zkc.Source.Structured.ProtocolPresentation
public meta import ZkcTools.StructuredSource.NormalizedRoot
public meta import ZkcTools.StructuredSource.Composition
public meta import ZkcTools.StructuredSource.ProcessReference
public meta import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.Companions

@[expose] public section

/-! Exact full equations for the actual randomized AND source. The normalizer
reads all sites, query order and masks from the admitted body. No ideal Sigma
process is substituted. Companions import this module, never conversely. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.MathematicalCompanionSigmaGoals
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs

named_values Inputs [firstBase, firstPoint, secondBase, secondPoint,
  firstWitness, secondWitness, nonceService, challengeService] := protocol0Signature.inputs
named_values Outputs [decision] := protocol0Signature.outputs
named_values RelationInputs [firstBase, firstPoint, secondBase, secondPoint,
  firstWitness, secondWitness] := helper0Helper.inputs

helper_presentation Relation
  inputs [firstBase, firstPoint, secondBase, secondPoint, firstWitness, secondWitness]
  outputs [decision] := helper0Body

abbrev signature : Signature := {}

def producer : NormalizedRoot.Checked program 0 signature := by
  derive_normalized_source_root

def validator : NormalizedRoot.Checked program 1 signature := by
  derive_normalized_source_root

named_values ProducerArguments [firstBase, firstPoint, secondBase, secondPoint,
  firstWitness, secondWitness, nonceService] := (NormalizedRoot.pattern program 0).scope
named_values ValidatorArguments [firstBase, firstPoint, secondBase, secondPoint,
  challengeService] := (NormalizedRoot.pattern program 1).scope

def producerArguments (model : DomainModel) (input : Inputs.View (Component model.Value)) :
    Binders model (NormalizedRoot.pattern program 0).scope :=
  ProducerArguments.pack
    { firstBase := input.firstBase, firstPoint := input.firstPoint,
      secondBase := input.secondBase, secondPoint := input.secondPoint,
      firstWitness := input.firstWitness, secondWitness := input.secondWitness,
      nonceService := input.nonceService }

def validatorArguments (model : DomainModel) (input : Inputs.View (Component model.Value)) :
    Binders model (NormalizedRoot.pattern program 1).scope :=
  ValidatorArguments.pack
    { firstBase := input.firstBase, firstPoint := input.firstPoint,
      secondBase := input.secondBase, secondPoint := input.secondPoint,
      challengeService := input.challengeService }

def presentedProducer (model : DomainModel) (input : Inputs.View (Component model.Value)) :=
  source_composition (NormalizedRoot.process producer model (producerArguments model input)
    (LawResults.empty model) (fun index => index.elim0))
    components [] atoms []

def presentedValidator (model : DomainModel) (input : Inputs.View (Component model.Value)) :=
  source_composition (NormalizedRoot.process validator model (validatorArguments model input)
    (LawResults.empty model) (fun index => index.elim0))
    components [] atoms []

source_reference producerReference from @presentedProducer using [presentedProducer]
source_reference validatorReference from @presentedValidator using [presentedValidator]

theorem actual_producer (model : DomainModel) (input : Inputs.View (Component model.Value)) :
    Occurrence.participant model program 0 (Inputs.pack input) = producerReference model input := by
  have masked : Occurrence.participant model program 0 (Inputs.pack input) =
      Occurrence.participant model program 0
        (NormalizedRoot.inputs model (producerArguments model input)) := by rfl
  rw [masked]
  refine (NormalizedRoot.equation producer model (producerArguments model input)
    (LawResults.empty model) (fun index => index.elim0)
    (fun index => index.elim0) (fun index => index.elim0)).trans ?_
  change NormalizedRoot.process producer model (producerArguments model input) _ _ = _
  refine Eq.trans ?_ (congrFun (congrFun producerReference_equation model) input)
  source_composition_equation atoms []

theorem actual_validator (model : DomainModel) (input : Inputs.View (Component model.Value)) :
    Occurrence.participant model program 1 (Inputs.pack input) = validatorReference model input := by
  have masked : Occurrence.participant model program 1 (Inputs.pack input) =
      Occurrence.participant model program 1
        (NormalizedRoot.inputs model (validatorArguments model input)) := by rfl
  rw [masked]
  refine (NormalizedRoot.equation validator model (validatorArguments model input)
    (LawResults.empty model) (fun index => index.elim0)
    (fun index => index.elim0) (fun index => index.elim0)).trans ?_
  change NormalizedRoot.process validator model (validatorArguments model input) _ _ = _
  refine Eq.trans ?_ (congrFun (congrFun validatorReference_equation model) input)
  source_composition_equation atoms []

end Tests.MathematicalCompanionSigmaGoals
