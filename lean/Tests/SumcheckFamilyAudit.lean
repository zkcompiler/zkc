module

import all Tests.SumcheckFamilyControls
import all Tests.SumcheckFamilyStops
import all Tests.SumcheckNativeConsumer
import all ZkcExamples.Executable.SumcheckFamilyBudget
import all ZkcExamples.Executable.SumcheckFamilySource
import all ZkcExamples.Executable.SumcheckFamilyResources
import all Zkc.Algebra.RingExpression.Basic
import all Zkc.Construction.ArtifactBinding
import all Zkc.Construction.ArtifactBindingTactic
import all Zkc.Construction.AuthoredPair
import all Zkc.Construction.AuthoredPairProducer
import all Zkc.Construction.Binding
import all Zkc.Construction.Compiled
import all Zkc.Construction.Context
import all Zkc.Construction.DomainBinding
import all Zkc.Construction.DomainCalculations
import all Zkc.Construction.DomainCorrespondence
import all Zkc.Construction.DomainExecution
import all Zkc.Construction.DomainExecutionLaws
import all Zkc.Construction.DomainProducer
import all Zkc.Construction.DomainTranscript
import all Zkc.Construction.DomainView
import all Zkc.Construction.DomainViewLaws
import all Zkc.Construction.FiatShamir
import all Zkc.Construction.OccurrenceResolution
import all Zkc.Construction.OriginProjection
import all Zkc.Construction.OriginalFold
import all Zkc.Construction.OriginalLaws
import all Zkc.Construction.OriginalRouting
import all Zkc.Construction.OriginalSimulation
import all Zkc.Construction.Participant
import all Zkc.Construction.Projection
import all Zkc.Construction.Rule
import all Zkc.Construction.Scalar
import all Zkc.Construction.ScalarAdapter
import all Zkc.Construction.ScalarLaws
import all Zkc.Construction.ScalarVerifier
import all Zkc.Construction.SourceDelivery
import all Zkc.Construction.SourceOccurrences
import all Zkc.Construction.Structured
import all Zkc.Construction.TransportReduction
import all Zkc.Construction.Uniform.DomainExecution
import all Zkc.Construction.Uniform.DomainHandler
import all Zkc.Construction.Uniform.DomainIteration
import all Zkc.Construction.Uniform.DomainProperties
import all Zkc.Executable.Cleanup
import all Zkc.Executable.Code
import all Zkc.Executable.Decoding
import all Zkc.Executable.DomainAnchorSemantics
import all Zkc.Executable.DomainByteLaws
import all Zkc.Executable.DomainCompleteness
import all Zkc.Executable.DomainFitsRules
import all Zkc.Executable.DomainHelpers
import all Zkc.Executable.DomainLowering
import all Zkc.Executable.DomainMotion
import all Zkc.Executable.DomainNativeBodyScopes
import all Zkc.Executable.DomainNativeByteTransport
import all Zkc.Executable.DomainNativeBytes
import all Zkc.Executable.DomainNativeCalculations
import all Zkc.Executable.DomainNativeCodeScope
import all Zkc.Executable.DomainNativeData
import all Zkc.Executable.DomainNativeEntry
import all Zkc.Executable.DomainNativeExecution
import all Zkc.Executable.DomainNativeHelperCosts
import all Zkc.Executable.DomainNativeHelpers
import all Zkc.Executable.DomainNativeLocalOperations
import all Zkc.Executable.DomainNativeLocalSoundness
import all Zkc.Executable.DomainNativeLoopScopes
import all Zkc.Executable.DomainNativeOccurrences
import all Zkc.Executable.DomainNativeOperationSoundness
import all Zkc.Executable.DomainNativeOperations
import all Zkc.Executable.DomainNativeReadback
import all Zkc.Executable.DomainNativeReadingLaws
import all Zkc.Executable.DomainNativeReceive
import all Zkc.Executable.DomainNativeRelation
import all Zkc.Executable.DomainNativeScope
import all Zkc.Executable.DomainNativeScopeLaws
import all Zkc.Executable.DomainNativeSoundness
import all Zkc.Executable.DomainNativeState
import all Zkc.Executable.DomainNativeTranscriptSteps
import all Zkc.Executable.DomainNativeUpdates
import all Zkc.Executable.DomainNormalization
import all Zkc.Executable.DomainNormalizationCheck
import all Zkc.Executable.DomainNormalizationSoundness
import all Zkc.Executable.DomainOrigins
import all Zkc.Executable.DomainParticipant
import all Zkc.Executable.DomainProcesses
import all Zkc.Executable.DomainSchema
import all Zkc.Executable.DomainSoundness
import all Zkc.Executable.DomainSuccess
import all Zkc.Executable.DomainSuccessRules
import all Zkc.Executable.DomainTermSemantics
import all Zkc.Executable.DomainVerifierTransport
import all Zkc.Executable.Evaluation
import all Zkc.Executable.Execution
import all Zkc.Executable.Framing
import all Zkc.Executable.HelperCosts
import all Zkc.Executable.HelperSchemas
import all Zkc.Executable.HelperSoundness
import all Zkc.Executable.Helpers
import all Zkc.Executable.Installed
import all Zkc.Executable.NativeLaws
import all Zkc.Executable.Numerical
import all Zkc.Executable.Observations
import all Zkc.Executable.Program
import all Zkc.Executable.Reading
import all Zkc.Executable.Refusal
import all Zkc.Executable.Relation
import all Zkc.Polynomial.BooleanCube
import all Zkc.Polynomial.Coordinates
import all Zkc.Polynomial.Multilinear
import all Zkc.Polynomial.Multilinear.ListRestriction
import all Zkc.Polynomial.Multilinear.Marginal
import all Zkc.Polynomial.Multilinear.Prefix
import all Zkc.Polynomial.Multilinear.Restriction
import all Zkc.Polynomial.Quadratic
import all Zkc.Protocols.Sumcheck.Multilinear.Fold
import all Zkc.Protocols.Sumcheck.Multilinear.Reduction
import all Zkc.Protocols.Sumcheck.Multilinear.Round
import all Zkc.Semantics.Boundary
import all Zkc.Semantics.ExactRefinement
import all Zkc.Semantics.Execution
import all Zkc.Semantics.ExecutionPath
import all Zkc.Semantics.Interaction
import all Zkc.Semantics.Interpretation
import all Zkc.Semantics.MonadExecution
import all Zkc.Semantics.StateInterpretation
import all Zkc.Semantics.Yields
import all Zkc.Source.Common
import all Zkc.Source.Common.Scalar
import all Zkc.Source.Common.Vocabulary
import all Zkc.Source.Component
import all Zkc.Source.ComponentCongruence
import all Zkc.Source.Context
import all Zkc.Source.ContextDecoding
import all Zkc.Source.ContextOperations
import all Zkc.Source.Decidable
import all Zkc.Source.DenotationLaws
import all Zkc.Source.DerivationLaws
import all Zkc.Source.DeriveRegion
import all Zkc.Source.Finite
import all Zkc.Source.Format
import all Zkc.Source.Interpretation
import all Zkc.Source.KernelRfl
import all Zkc.Source.Mathematical
import all Zkc.Source.Mathematical.Projection
import all Zkc.Source.Participant
import all Zkc.Source.Program
import all Zkc.Source.Region
import all Zkc.Source.RegionCongruence
import all Zkc.Source.RegionContracts
import all Zkc.Source.RegionDecoding
import all Zkc.Source.RegionDerivation
import all Zkc.Source.RegionInterpretation
import all Zkc.Source.RegionTotality
import all Zkc.Source.RoleFamily
import all Zkc.Source.ScalarRegion
import all Zkc.Source.Structure
import all Zkc.Source.Structured.Admission
import all Zkc.Source.Structured.Algebra
import all Zkc.Source.Structured.ApplicationMetadata
import all Zkc.Source.Structured.Association
import all Zkc.Source.Structured.Availability
import all Zkc.Source.Structured.Catalogue
import all Zkc.Source.Structured.Checked
import all Zkc.Source.Structured.CheckedData
import all Zkc.Source.Structured.ClosedProfile
import all Zkc.Source.Structured.CommonAdapter
import all Zkc.Source.Structured.Component
import all Zkc.Source.Structured.ComponentLinking
import all Zkc.Source.Structured.ContractAdmission
import all Zkc.Source.Structured.ContractBinding
import all Zkc.Source.Structured.ContractBoundary
import all Zkc.Source.Structured.ContractCalls
import all Zkc.Source.Structured.ContractComposition
import all Zkc.Source.Structured.ContractInstantiation
import all Zkc.Source.Structured.DerivationRules
import all Zkc.Source.Structured.DomainComponent
import all Zkc.Source.Structured.DomainEvaluation
import all Zkc.Source.Structured.DomainInterpretation
import all Zkc.Source.Structured.DomainModels
import all Zkc.Source.Structured.DomainParticipant
import all Zkc.Source.Structured.DomainParticipantInterpretation
import all Zkc.Source.Structured.Evaluation
import all Zkc.Source.Structured.Format
import all Zkc.Source.Structured.Formation
import all Zkc.Source.Structured.Frame
import all Zkc.Source.Structured.HelperSources
import all Zkc.Source.Structured.Import
import all Zkc.Source.Structured.Interpretation
import all Zkc.Source.Structured.IterationObservations
import all Zkc.Source.Structured.Laws
import all Zkc.Source.Structured.Limits
import all Zkc.Source.Structured.Linking
import all Zkc.Source.Structured.MapEvaluation
import all Zkc.Source.Structured.MapLaws
import all Zkc.Source.Structured.Meaning
import all Zkc.Source.Structured.NaturalPowerOfTwo
import all Zkc.Source.Structured.NormalForm.Denote
import all Zkc.Source.Structured.NormalForm.Normalize
import all Zkc.Source.Structured.NormalForm.Presentation
import all Zkc.Source.Structured.NormalForm.Soundness
import all Zkc.Source.Structured.NormalForm.Syntax
import all Zkc.Source.Structured.Occurrence
import all Zkc.Source.Structured.OpenAdmission
import all Zkc.Source.Structured.OpenLaws
import all Zkc.Source.Structured.OpenMeaning
import all Zkc.Source.Structured.Operations
import all Zkc.Source.Structured.Origin
import all Zkc.Source.Structured.OutputSelection
import all Zkc.Source.Structured.Participant
import all Zkc.Source.Structured.PreparationAdmission
import all Zkc.Source.Structured.PrimitiveEvaluation
import all Zkc.Source.Structured.PrimitiveLaws
import all Zkc.Source.Structured.Primitives
import all Zkc.Source.Structured.ProtocolAdmission
import all Zkc.Source.Structured.ProtocolContext
import all Zkc.Source.Structured.ProtocolLinking
import all Zkc.Source.Structured.ProtocolOperations
import all Zkc.Source.Structured.ProtocolScopes
import all Zkc.Source.Structured.ProtocolSignature
import all Zkc.Source.Structured.ProtocolTable
import all Zkc.Source.Structured.Provenance
import all Zkc.Source.Structured.Repeat
import all Zkc.Source.Structured.RepeatAdmission
import all Zkc.Source.Structured.RepeatLaws
import all Zkc.Source.Structured.Table
import all Zkc.Source.Structured.UnitViews
import all Zkc.Source.Structured.Vocabulary
import all Zkc.Specification
import all Zkc.Transcript.Interface
import all ZkcExamples.Construction.Generated.SmallSumcheckPair
import all ZkcExamples.Construction.SumcheckArtifact
import all ZkcExamples.Construction.SumcheckDomainConnection
import all ZkcExamples.Construction.SumcheckDomainControls
import all ZkcExamples.Construction.SumcheckDomainLoop
import all ZkcExamples.Construction.SumcheckDomainRoot
import all ZkcExamples.Construction.SumcheckDomainRound
import all ZkcExamples.Construction.SumcheckDomainVerifier
import all ZkcExamples.Construction.SumcheckProof
import all ZkcExamples.Construction.SumcheckProofParticipant
import all ZkcExamples.Construction.SumcheckScalarProtocol
import all ZkcExamples.Construction.SumcheckScalarRound
import all ZkcExamples.Construction.SumcheckSourceConnection
import all ZkcExamples.Executable.SumcheckCharges
import all ZkcExamples.Executable.SumcheckCompleteness
import all ZkcExamples.Executable.SumcheckDomainHonest
import all ZkcExamples.Executable.SumcheckFamily
import all ZkcExamples.Executable.SumcheckHelpers
import all ZkcExamples.Executable.SumcheckMessages
import all ZkcExamples.Executable.SumcheckMetadata
import all ZkcExamples.Executable.SumcheckProof
import all ZkcExamples.Executable.SumcheckProofFacts
import all ZkcExamples.Executable.SumcheckProofProgramData
import all ZkcExamples.Executable.SumcheckShape
import all ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import all ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
import all ZkcExamples.Structured.MapFirstBodies
import all ZkcExamples.Structured.MapFirstContracts
import all ZkcExamples.Structured.MapFirstLaws
import all ZkcExamples.Structured.MapPrefixBodies
import all ZkcExamples.Structured.MapPrefixContracts
import all ZkcExamples.Structured.MapPrefixLaws
import all ZkcExamples.Structured.MapProjectionContracts
import all ZkcExamples.Structured.MapSourceExpansions
import all ZkcExamples.Structured.NormalFormSteps
import all ZkcExamples.Structured.PrimitiveExpansions
import all ZkcExamples.Structured.PrimitiveHalvesData
import all ZkcExamples.Structured.PrimitiveHalvesViews
import all ZkcExamples.Structured.PrimitiveLibrary
import all ZkcExamples.Structured.PrimitiveRows
import all ZkcExamples.Structured.PrimitiveSequenceData
import all ZkcExamples.Structured.PrimitiveSequenceViews
import all ZkcExamples.Structured.PrimitiveShapeData
import all ZkcExamples.Structured.PrimitiveShapeViews
import all ZkcExamples.Structured.PrimitiveTableData
import all ZkcExamples.Structured.PrimitiveTableViews
import all ZkcExamples.Structured.SumcheckHelperBodies
import all ZkcExamples.Structured.SumcheckHelperBridge
import all ZkcExamples.Structured.SumcheckHelperExpansions
import all ZkcExamples.Structured.SumcheckHelperLaws
import all ZkcExamples.Structured.SumcheckRelationContract
import all ZkcExamples.Structured.SumcheckRoundLaws
import all ZkcExamples.Structured.SumcheckRoundNormalForms
import all ZkcExamples.Structured.SumcheckSourceAssociations
import all ZkcExamples.Structured.SumcheckSourceBodies
import all ZkcExamples.Structured.SumcheckSourceContracts
import all ZkcExamples.Structured.SumcheckSourceData
import all ZkcExamples.Structured.SumcheckSourceLaws
import all ZkcExamples.Structured.SumcheckSourceNormalForms
import all ZkcExamples.Structured.SumcheckSourceVerifier
import all ZkcExamples.Structured.SumcheckSourceViews
import all ZkcExamples.Structured.SumcheckUnitContracts
import all ZkcExamples.Structured.SumcheckVerifierBodies
import all ZkcExamples.Structured.SumcheckVerifierHelpers
import all ZkcExamples.Structured.SumcheckVerifierLaws
import all ZkcExamples.Structured.SumcheckVerifierPrelude
import all ZkcExamples.Structured.SumcheckVerifierProcess
import all ZkcExamples.Structured.SumcheckVerifierTerminal
public import Lean.Util.FoldConsts

/-! Strict type/body auditing. Ownership is determined by the defining module,
so project PIR declarations are checked even though their names lack Zkc. -/
set_option maxHeartbeats 0
open Lean Elab Command

private def owner (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.modules[index.toNat]!.module
  | none => env.mainModule

private def projectModule (name : Name) : Bool :=
  [`Zkc, `ZkcExamples, `Tests].any (·.isPrefixOf name)

private def forbidden (name : Name) : Bool :=
  #[`Zkc.Construction.specK, `Zkc.Construction.specStep, `Zkc.Construction.spec,
    `Zkc.Construction.idealK, `Zkc.Construction.idealStep, `Zkc.Construction.ideal,
    `Zkc.Executable.meteredK, `Zkc.Executable.meteredStep, `Zkc.Executable.meteredIterate,
    `Zkc.Executable.metered, `Zkc.Executable.FitsK, `Zkc.Executable.FitsStep, `Zkc.Executable.FitsIterate,
    `Zkc.Executable.Sufficient, `Zkc.Executable.Succeeds,
    `Zkc.Construction.Uniform.compiled_selected, `sorryAx].any fun root =>
      root.isPrefixOf name || name.toString.startsWith (root.toString ++ "_")

private def closure (root : Name) : CommandElabM (Array Name) := do
  let env := (← getEnv).setExporting false
  let mut seen : NameSet := {}
  let mut result := #[]
  let mut pending := [root]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | throwError "unresolved dependency: {name}"
    if forbidden name then throwError "retired interpreter dependency: {name}"
    result := result.push name
    -- Imported libraries are the upstream body boundary. Every project type
    -- and opaque body must be present; no unresolved name is an allowed leaf.
    if projectModule (owner env name) then
      if info.isAxiom then throwError "project body unavailable: {name} (owner {owner env name})"
      if info.isUnsafe then throwError "unsafe project declaration: {name}"
      for used in info.getUsedConstantsAsSet do pending := used :: pending
  return result

private theorem bodyMarker : True := True.intro
private theorem bodyWitness : True := bodyMarker
private theorem PIR.ownerWitness : True := bodyMarker

run_cmd do
  let body ← closure ``bodyWitness
  unless body.contains ``bodyMarker do throwError "body traversal missed marker"
  let env ← getEnv
  unless projectModule (owner env ``PIR.ownerWitness) &&
      projectModule (owner env `PIR.Process.bind) do
    throwError "defining-module ownership missed PIR"
  let missingRejected ← try
    let _ ← closure `Tests.SumcheckFamilyAudit.missing
    pure false
  catch _ => pure true
  unless missingRejected do throwError "unresolved dependency accepted"
  unless forbidden `Zkc.Construction.specK && forbidden `Zkc.Executable.metered.eq_1 do
    throwError "retired-interpreter classifier failed"

run_cmd do
  let forbiddenAdmissions := #[`Zkc.Executable.DomainVM.Passes, `Zkc.Executable.DomainVM.metered,
    `Zkc.Executable.DomainVM.observation, `ZkcExamples.Executable.SumcheckFamily.ProgramShape.Contract]
  let env := (← getEnv).setExporting false
  for constructor in #[`ZkcExamples.Executable.SumcheckFamily.Artifact.mk,
      `ZkcExamples.Executable.SumcheckFamily.Realization.mk,
      `ZkcExamples.Executable.SumcheckFamily.Source.Helpers.mk,
      `ZkcExamples.Executable.SumcheckFamily.Source.Prices.mk,
      `ZkcExamples.Executable.SumcheckFamily.Source.Occurrences.mk] do
    let some info := env.checked.get.find? constructor | throwError "missing constructor: {constructor}"
    for used in info.type.getUsedConstantsAsSet do
      if forbiddenAdmissions.contains used then throwError "whole-run admission: {constructor}: {used}"
    logInfo m!"LOCAL ADMISSION TYPE {constructor}: {info.type}"

run_cmd do
  let roots := #[
    `ZkcExamples.Executable.SumcheckProof.prepared,
    `ZkcExamples.Executable.SumcheckProof.helpersSorted,
    `ZkcExamples.Executable.SumcheckProof.native_checked,
    `ZkcExamples.Executable.SumcheckProof.embedded,
    `ZkcExamples.Executable.SumcheckProof.normalized,
    `ZkcExamples.Executable.SumcheckProof.executable_metered,
    `ZkcExamples.Executable.SumcheckProof.domain_prunes,
    `ZkcExamples.Executable.SumcheckProof.executable_transform_prunes,
    `ZkcExamples.Executable.SumcheckFamily.ProgramShape.sufficient,
    `ZkcExamples.Executable.SumcheckFamily.ProgramShape.honest_success,
    `ZkcExamples.Executable.SumcheckCharges.programContract,
    `ZkcExamples.Executable.SumcheckCharges.sufficient,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_decoded,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_metered_bytes,
    `Tests.SumcheckNativeConsumer.selected_honest,
    `Tests.SumcheckNativeConsumer.zero_honest,
    `Tests.SumcheckNativeConsumer.one_honest,
    `Tests.SumcheckNativeConsumer.two_honest,
    `Tests.SumcheckNativeConsumer.wrong_header,
    `Tests.SumcheckNativeConsumer.zero_budget,
    `ZkcExamples.Executable.SumcheckFamily.Source.round_projection,
    `ZkcExamples.Executable.SumcheckFamily.Source.loop_projection,
    `ZkcExamples.Executable.SumcheckFamily.Source.mapped_messages,
    `ZkcExamples.Executable.SumcheckFamily.Source.mapped_round,
    `ZkcExamples.Executable.SumcheckFamily.Source.round_passes,
    `ZkcExamples.Executable.SumcheckFamily.Source.honest_step,
    `ZkcExamples.Executable.SumcheckFamily.Source.reduce_passes,
    `ZkcExamples.Executable.SumcheckFamily.Source.observation_passes,
    `ZkcExamples.Executable.SumcheckFamily.Source.round_fits,
    `ZkcExamples.Executable.SumcheckFamily.Source.budgetContract,
    `ZkcExamples.Executable.SumcheckFamily.honest_metered,
    `ZkcExamples.Executable.SumcheckFamily.receive_types,
    `ZkcExamples.Executable.SumcheckFamily.honest_accepted,
    `ZkcExamples.Executable.SumcheckCharges.sufficient_family,
    `ZkcExamples.Executable.SumcheckDomainHonest.programOccurrences,
    `ZkcExamples.Executable.SumcheckDomainHonest.programHelpers,
    `ZkcExamples.Executable.SumcheckDomainHonest.programPrices,
    `ZkcExamples.Executable.SumcheckDomainHonest.realization,
    `ZkcExamples.Executable.SumcheckDomainHonest.observation_passes,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_metered,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_accepted,
    `Tests.SumcheckFamilyControls.alternate_checked,
    `Tests.SumcheckFamilyControls.entries_differ,
    `Tests.SumcheckFamilyControls.oracle_keys_differ,
    `Tests.SumcheckFamilyControls.alternateOccurrences,
    `Tests.SumcheckFamilyControls.helper_functions_agree,
    `Tests.SumcheckFamilyControls.alternateRealization,
    `Tests.SumcheckFamilyControls.alternate_three_accepted,
    `Tests.SumcheckFamilyControls.alternate_zero_accepted,
    `Tests.SumcheckFamilyStops.missing_first,
    `Tests.SumcheckFamilyStops.wrong_first,
    `Tests.SumcheckFamilyStops.missing_second,
    `Tests.SumcheckFamilyStops.wrong_second,
    `Tests.SumcheckFamilyStops.false_round,
    `Tests.SumcheckFamilyStops.unreadable_suffix,
    `Tests.SumcheckFamilyStops.old_origin_presence,
    `Tests.SumcheckFamilyStops.malformed_query_none,
    `Tests.SumcheckFamilyStops.malformed_occurrences_impossible,
    `Tests.SumcheckFamilyStops.malformed_native_refused,
    `Tests.SumcheckFamilyStops.short_binding_header]
  let env := (← getEnv).setExporting false
  for root in roots do
    let names ← closure root
    let some info := env.checked.get.find? root | throwError "missing root: {root}"
    let axioms ← collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "nonstandard axioms in {root}: {axioms}"
    if #[`ZkcExamples.Executable.SumcheckFamily.honest_accepted,
        `ZkcExamples.Executable.SumcheckFamily.honest_metered,
        `ZkcExamples.Executable.SumcheckFamily.Source.observation_passes].contains root then
      for used in names do
        if #[`ZkcExamples.Construction.SumcheckProof, `ZkcExamples.Construction.SumcheckDomainConnection,
            `ZkcExamples.Executable.SumcheckProof, `ZkcExamples.Executable.SumcheckHelpers,
            `ZkcExamples.Executable.SumcheckDomainHonest,
            `ZkcExamples.Executable.SumcheckFamily.ProgramShape.honest_success,
            `ZkcExamples.Executable.SumcheckCharges.programShape].any (·.isPrefixOf used) then
          throwError "concrete subject or success-combinator dependency in generic theorem: {root}: {used}"
    logInfo m!"STORED TYPE {root}: {info.type}"
    logInfo m!"PASS {root}: dependencies={names.size}; unresolved=0; forbidden=0; axioms={axioms}"
  logInfo m!"SUMCHECK-FAMILY-AUDIT-PASS roots={roots.size}"
