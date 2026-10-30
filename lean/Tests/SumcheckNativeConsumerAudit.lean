module
import all Zkc.Source.Structured.Bindings.Assembly
import all Zkc.Source.Structured.Bindings.Component
import all Zkc.Source.Structured.Bindings.Selection
import all Zkc.Source.Structured.LoopPresentation
import all Zkc.Source.Structured.NormalForm.Sites
import all Zkc.Source.Structured.OccurrencePresentation
import all Zkc.Source.Structured.ProtocolPresentation
import all ZkcExamples.Structured.Generated.Scalar.SumcheckSource
import all ZkcExamples.Structured.Generated.Scalar.SumcheckSourceBindings
import all ZkcExamples.Structured.Generated.Scalar.SumcheckSourceBindingsCallbacks
import all ZkcExamples.Structured.Generated.Scalar.SumcheckSourceLibrary
import all ZkcTools.ConstructionBindings.Alignment
import all ZkcTools.ConstructionBindings.Inputs
import all ZkcTools.ConstructionBindings.LibraryBuilder
import all ZkcTools.ConstructionBindings.LibraryPlan
import all ZkcTools.ConstructionBindings.Readback
import all ZkcTools.ConstructionBindings.Root
import all ZkcTools.ConstructionBindings.Syntax
import all Zkc.Source.Structured.ReferenceLaws
import all Zkc.Source.Structured.ReferenceLibrary
import all Zkc.Source.Structured.MultilinearBodies
import all Zkc.Source.Structured.MultilinearReference
import all Zkc.Source.Structured.MultilinearAdmissionReference
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.Source.Structured.RelationChecking
import all Zkc.Source.Structured.FiniteDomains
import all Zkc.Source.Structured.CollectionReferenceLaws
import all Zkc.Source.Structured.CollectEvaluation
import all Zkc.Source.Structured.CollectLaws
import all Zkc.Protocols.Multilinear.Source.CollectBodies
import all Zkc.Protocols.Multilinear.Source.CollectLaws
import all Zkc.Protocols.Multilinear.Source.PrefixBodies
import all Zkc.Protocols.Sumcheck.Source.DomainHelpers

import all Tests.SumcheckNativeConsumer
import all Zkc.Algebra.RingExpression.Basic
import all Zkc.Construction.ArtifactBinding
import all ZkcTools.ConstructionBindings.ArtifactBindingTactic
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
import all Zkc.Construction.InputSelection
import all Zkc.Construction.Rule
import all Zkc.Construction.Scalar
import all Zkc.Construction.ScalarAdapter
import all Zkc.Construction.ScalarLaws
import all Zkc.Construction.ScalarVerifier
import all Zkc.Construction.SourceDelivery
import all Zkc.Construction.SourceOccurrences
import all Zkc.Construction.Structured
import all ZkcTools.ConstructionBindings.TransportReduction
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
import all Zkc.Source.Structured.PlainHelpers
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
import all ZkcExamples.Construction.SumcheckProof
import all ZkcExamples.Construction.SumcheckProofParticipant
import all ZkcExamples.Construction.SumcheckSourceConnection
import all ZkcExamples.Executable.SumcheckCharges
import all ZkcExamples.Executable.SumcheckCompleteness
import all ZkcExamples.Executable.SumcheckDomainHonest
import all ZkcExamples.Executable.SumcheckFamily
import all ZkcExamples.Executable.SumcheckFamilyBudget
import all ZkcExamples.Executable.SumcheckFamilySource
import all ZkcExamples.Executable.SumcheckFamilyResources
import all ZkcExamples.Executable.SumcheckHelpers
import all ZkcExamples.Executable.SumcheckMessages
import all ZkcExamples.Executable.SumcheckMetadata
import all ZkcExamples.Executable.SumcheckProof
import all ZkcExamples.Executable.SumcheckProofFacts
import all ZkcExamples.Executable.SumcheckProofProgramData
import all ZkcExamples.Executable.SumcheckShape
import all ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import all ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
import all Zkc.Protocols.Multilinear.Source.MapFirstBodies
import all Zkc.Protocols.Multilinear.Source.MapFirstContracts
import all Zkc.Protocols.Multilinear.Source.MapFirstLaws
import all Zkc.Protocols.Multilinear.Source.MapPrefixBodies
import all Zkc.Protocols.Multilinear.Source.MapPrefixContracts
import all Zkc.Protocols.Multilinear.Source.MapPrefixLaws
import all Zkc.Protocols.Multilinear.Source.MapProjectionContracts
import all Zkc.Protocols.Multilinear.Source.MapSourceExpansions
import all Zkc.Source.Structured.NormalForm.Steps
import all ZkcExamples.Structured.PrimitiveExpansions
import all ZkcExamples.Structured.PrimitiveHalvesData
import all ZkcExamples.Structured.PrimitiveHalvesViews
import all Zkc.Protocols.Multilinear.Source.PrimitiveLibrary
import all Zkc.Protocols.Multilinear.Source.PrimitiveRows
import all ZkcExamples.Structured.PrimitiveSequenceData
import all ZkcExamples.Structured.PrimitiveSequenceViews
import all ZkcExamples.Structured.PrimitiveShapeData
import all ZkcExamples.Structured.PrimitiveShapeViews
import all ZkcExamples.Structured.PrimitiveTableData
import all ZkcExamples.Structured.PrimitiveTableViews
import all Zkc.Protocols.Sumcheck.Source.HelperBodies
import all Zkc.Protocols.Sumcheck.Source.HelperBridge
import all Zkc.Protocols.Sumcheck.Source.HelperExpansions
import all Zkc.Protocols.Sumcheck.Source.HelperLaws
import all Zkc.Protocols.Sumcheck.Source.PendingLaws
import all Zkc.Protocols.Sumcheck.Source.PreludeNormalForms
import all ZkcExamples.Structured.SumcheckRelationContract
import all Zkc.Protocols.Sumcheck.Source.RoundLaws
import all Zkc.Protocols.Sumcheck.Source.RoundNormalForms
import all ZkcExamples.Structured.SumcheckSourceAssociations
import all ZkcExamples.Structured.SumcheckSourceBodies
import all ZkcExamples.Structured.SumcheckSourceContracts
import all ZkcExamples.Structured.SumcheckSourceData
import all ZkcExamples.Structured.SumcheckSourceLaws
import all ZkcExamples.Structured.SumcheckSourceNormalForms
import all ZkcExamples.Structured.SumcheckSourceVerifier
import all ZkcExamples.Structured.SumcheckSourceViews
import all Zkc.Protocols.Sumcheck.Source.UnitContracts
import all Zkc.Protocols.Sumcheck.Source.VerifierBodies
import all Zkc.Protocols.Sumcheck.Source.VerifierHelpers
import all Zkc.Protocols.Sumcheck.Source.VerifierLaws
import all Zkc.Protocols.Sumcheck.Source.VerifierPrelude
import all Zkc.Protocols.Sumcheck.Source.VerifierProcess
import all ZkcExamples.Structured.SumcheckVerifierTerminal
import all Zkc.Construction.ConnectionActionCoverage
import all Zkc.Construction.ConnectionActionSupport
import all Zkc.Construction.ConnectionActions
import all Zkc.Construction.ConnectionAdmission
import all Zkc.Construction.ConnectionApplicationCoverageFrame
import all Zkc.Construction.ConnectionApplicationFrame
import all Zkc.Construction.ConnectionApplications
import all Zkc.Construction.ConnectionCalculations
import all Zkc.Construction.ConnectionCertificate
import all Zkc.Construction.ConnectionCertificateAdmission
import all Zkc.Construction.ConnectionComputation
import all Zkc.Construction.ConnectionContext
import all Zkc.Construction.ConnectionCoordinates
import all Zkc.Construction.ConnectionFrame
import all Zkc.Construction.ConnectionHelperCalculation
import all Zkc.Construction.ConnectionHelperProjection
import all Zkc.Construction.ConnectionHelpers
import all Zkc.Construction.ConnectionInputFrames
import all Zkc.Construction.ConnectionInputLayout
import all Zkc.Construction.ConnectionInputSchema
import all Zkc.Construction.ConnectionInputs
import all Zkc.Construction.ConnectionInstallation
import all Zkc.Construction.ConnectionLayout
import all Zkc.Construction.ConnectionLibrary
import all Zkc.Construction.ConnectionLoopFrames
import all Zkc.Construction.ConnectionLoops
import all Zkc.Construction.ConnectionMasking
import all Zkc.Construction.ConnectionObservationPrefix
import all Zkc.Construction.ConnectionObservations
import all Zkc.Construction.ConnectionOrigins
import all Zkc.Construction.ConnectionOutputSelection
import all Zkc.Construction.ConnectionOutputs
import all Zkc.Construction.ConnectionPresence
import all Zkc.Construction.ConnectionProjectedContinuation
import all Zkc.Construction.ConnectionReturnProjection
import all Zkc.Construction.ConnectionProjectedFrames
import all Zkc.Construction.ConnectionProjectedLoops
import all Zkc.Construction.ConnectionRepeatSupport
import all Zkc.Construction.ConnectionRoot
import all Zkc.Construction.ConnectionRootCertificate
import all Zkc.Construction.ConnectionRootInputs
import all Zkc.Construction.ConnectionRootRoutes
import all Zkc.Construction.ConnectionRouteCoverage
import all Zkc.Construction.ConnectionRouteCoverageFrames
import all Zkc.Construction.ConnectionRouteCoverageLoops
import all Zkc.Construction.ConnectionRouteCoverageRoot
import all Zkc.Construction.ConnectionRouteCoverageSupport
import all Zkc.Construction.ConnectionRouting
import all Zkc.Construction.ConnectionStaticRoutes
import all Zkc.Construction.ConnectionSubstitution
import all Zkc.Construction.ConnectionTargetExtent
import all Zkc.Construction.ConnectionTargetPrefix
import all Zkc.Construction.ConnectionTranscript
import all Zkc.Construction.OriginalABI
import all Zkc.Construction.OriginalEffects
import all Zkc.Construction.OriginalFrameRelations
import all Zkc.Construction.OriginalHeadReduction
import all Zkc.Construction.OriginalHelperEncoding
import all Zkc.Construction.OriginalHelpers
import all Zkc.Construction.OriginalInputs
import all Zkc.Construction.OriginalLoop
import all Zkc.Construction.OriginalParticipant
import all Zkc.Construction.PairAcceptance
import all Zkc.Construction.ScalarConnection
import all Zkc.Construction.SourceConnection
import all Zkc.Construction.Uniform.LoopedSourceProcess
import all Zkc.Construction.Uniform.ScalarCheckedBytes
import all Zkc.Construction.Uniform.ScalarCheckedFrames
import all Zkc.Construction.Uniform.ScalarFragment
import all Zkc.Construction.Uniform.ScalarHandles
import all Zkc.Construction.Uniform.ScalarObservation
import all Zkc.Construction.Uniform.ScalarProjection
import all Zkc.Construction.Uniform.ScalarSourceCost
import all Zkc.Construction.Uniform.ScalarSupport
import all Zkc.Construction.Uniform.ScalarSupportProposer
import all Zkc.Construction.Uniform.SourceProcess
import all Zkc.Semantics.OperationSupport
import all Zkc.Source.OperationSupport
import all Zkc.Source.Structured.BodyBindings
import all Zkc.Source.Structured.ComponentClosure
import all Zkc.Source.Structured.ComponentDeclarations
import all Zkc.Source.Structured.DomainFrame
import all Zkc.Source.Structured.DomainLinking
import all Zkc.Source.Structured.DomainProtocolLinking
import all Zkc.Source.Structured.InputVisibility
import all Zkc.Source.Structured.NormalForm.Observation
import all ZkcExamples.Executable.SumcheckCheckedRound
import all ZkcExamples.Executable.SumcheckSourceHonest
import all ZkcExamples.Structured.Generated.Connections.SmallSumcheck
import all ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
import all Zkc.Protocols.Multilinear.Source.Bindings
import all Zkc.Protocols.Sumcheck.Source.Checks
import all Zkc.Protocols.Sumcheck.Source.Library
import all ZkcExamples.Structured.SumcheckMathBindings
import all Zkc.Protocols.Sumcheck.Source.PendingBodies
import all Zkc.Protocols.Sumcheck.Source.ProverLaws
import all Zkc.Protocols.Sumcheck.Source.ProverProcess
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
    let _ ← closure `Tests.SumcheckNativeConsumerAudit.missing
    pure false
  catch _ => pure true
  unless missingRejected do throwError "unresolved dependency accepted"
  unless forbidden `Zkc.Construction.specK && forbidden `Zkc.Executable.metered.eq_1 do
    throwError "retired-interpreter classifier failed"

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
    `ZkcExamples.Executable.SumcheckCharges.sufficient_family,
    `ZkcExamples.Executable.SumcheckCharges.sufficient,
    `ZkcExamples.Executable.SumcheckDomainHonest.observation_passes,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_metered,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_decoded,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_metered_bytes,
    `ZkcExamples.Executable.SumcheckCompleteness.honest_accepted,
    `Tests.SumcheckNativeConsumer.selected_honest,
    `Tests.SumcheckNativeConsumer.zero_honest,
    `Tests.SumcheckNativeConsumer.one_honest,
    `Tests.SumcheckNativeConsumer.two_honest,
    `Tests.SumcheckNativeConsumer.wrong_header,
    `Tests.SumcheckNativeConsumer.zero_budget]
  let env := (← getEnv).setExporting false
  for root in roots do
    let names ← closure root
    let some info := env.checked.get.find? root | throwError "missing root: {root}"
    let axioms ← collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "nonstandard axioms in {root}: {axioms}"
    logInfo m!"STORED TYPE {root}: {info.type}"
    logInfo m!"PASS {root}: dependencies={names.size}; unresolved=0; forbidden=0; axioms={axioms}"
  logInfo m!"SUMCHECK-NATIVE-CONSUMER-AUDIT-PASS roots={roots.size}"
