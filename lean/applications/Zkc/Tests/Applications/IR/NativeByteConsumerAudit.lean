module
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.IR.Source.Structured.RelationChecking
import all Zkc.Tests.Applications.IR.NativeByteConsumers
import all Zkc.Program.Algebra.RingExpression.Basic
import all Zkc.IR.Construction.ArtifactBinding
import all Zkc.Tools.IR.ConstructionBindings.ArtifactBindingTactic
import all Zkc.IR.Construction.AuthoredPair
import all Zkc.IR.Construction.AuthoredPairProducer
import all Zkc.IR.Construction.Binding
import all Zkc.IR.Construction.Compiled
import all Zkc.IR.Construction.Context
import all Zkc.IR.Construction.ConnectionFrameLookup
import all Zkc.IR.Construction.DomainBinding
import all Zkc.IR.Construction.DomainCalculations
import all Zkc.IR.Construction.DomainCorrespondence
import all Zkc.IR.Construction.DomainExecution
import all Zkc.IR.Construction.DomainExecutionLaws
import all Zkc.IR.Construction.DomainProducer
import all Zkc.IR.Construction.DomainTranscript
import all Zkc.IR.Construction.DomainView
import all Zkc.IR.Construction.DomainViewLaws
import all Zkc.IR.Construction.FiatShamir
import all Zkc.IR.Construction.OccurrenceResolution
import all Zkc.IR.Construction.OriginProjection
import all Zkc.IR.Construction.OriginalFold
import all Zkc.IR.Construction.OriginalLaws
import all Zkc.IR.Construction.OriginalRouting
import all Zkc.IR.Construction.OriginalSimulation
import all Zkc.IR.Construction.Participant
import all Zkc.IR.Construction.InputSelection
import all Zkc.IR.Construction.Rule
import all Zkc.IR.Construction.Scalar
import all Zkc.IR.Construction.ScalarAdapter
import all Zkc.IR.Construction.ScalarLaws
import all Zkc.IR.Construction.ScalarVerifier
import all Zkc.IR.Construction.SourceDelivery
import all Zkc.IR.Construction.SourceOccurrences
import all Zkc.IR.Construction.Structured
import all Zkc.Tools.Program.ConstructionBindings.TransportReduction
import all Zkc.IR.Construction.Uniform.DomainExecution
import all Zkc.IR.Construction.Uniform.DomainHandler
import all Zkc.IR.Construction.Uniform.DomainProperties
import all Zkc.IR.Construction.Uniform.SourceProcess
import all Zkc.Tools.IR.ConstructionBindings.ScalarConnection
import all Zkc.IR.Executable.ByteParticipantTransport
import all Zkc.IR.Executable.Code
import all Zkc.IR.Executable.Decoding
import all Zkc.IR.Executable.DomainAnchorSemantics
import all Zkc.IR.Executable.DomainByteLaws
import all Zkc.IR.Executable.DomainCompleteness
import all Zkc.IR.Executable.DomainHelpers
import all Zkc.IR.Executable.DomainLowering
import all Zkc.IR.Executable.DomainMotion
import all Zkc.IR.Executable.DomainNativeBodyScopes
import all Zkc.IR.Executable.DomainNativeByteTransport
import all Zkc.IR.Executable.DomainNativeBytes
import all Zkc.IR.Executable.DomainNativeCalculations
import all Zkc.IR.Executable.DomainNativeCodeScope
import all Zkc.IR.Executable.DomainNativeData
import all Zkc.IR.Executable.DomainNativeEntry
import all Zkc.IR.Executable.DomainNativeExecution
import all Zkc.IR.Executable.DomainNativeHelperCosts
import all Zkc.IR.Executable.DomainNativeHelpers
import all Zkc.IR.Executable.DomainNativeLocalOperations
import all Zkc.IR.Executable.DomainNativeLocalSoundness
import all Zkc.IR.Executable.DomainNativeLoopScopes
import all Zkc.IR.Executable.DomainNativeOccurrences
import all Zkc.IR.Executable.DomainNativeOperationSoundness
import all Zkc.IR.Executable.DomainNativeOperations
import all Zkc.IR.Executable.DomainNativeReadback
import all Zkc.IR.Executable.DomainNativeReadingLaws
import all Zkc.IR.Executable.DomainNativeReceive
import all Zkc.IR.Executable.DomainNativeRelation
import all Zkc.IR.Executable.DomainNativeScope
import all Zkc.IR.Executable.DomainNativeScopeLaws
import all Zkc.IR.Executable.DomainNativeSoundness
import all Zkc.IR.Executable.DomainNativeState
import all Zkc.IR.Executable.DomainNativeTranscriptSteps
import all Zkc.IR.Executable.DomainNativeUpdates
import all Zkc.IR.Executable.DomainNormalization
import all Zkc.IR.Executable.DomainNormalizationCheck
import all Zkc.IR.Executable.DomainNormalizationSoundness
import all Zkc.IR.Executable.DomainOrigins
import all Zkc.IR.Executable.DomainParticipant
import all Zkc.IR.Executable.DomainProcesses
import all Zkc.IR.Executable.DomainSchema
import all Zkc.IR.Executable.DomainSoundness
import all Zkc.IR.Executable.DomainTermSemantics
import all Zkc.IR.Executable.DomainVerifierTransport
import all Zkc.IR.Executable.Evaluation
import all Zkc.IR.Executable.Execution
import all Zkc.IR.Executable.Framing
import all Zkc.IR.Executable.HelperSoundness
import all Zkc.IR.Executable.Helpers
import all Zkc.IR.Executable.Installed
import all Zkc.IR.Executable.NativeLaws
import all Zkc.IR.Executable.HelperSchemas
import all Zkc.IR.Executable.Numerical
import all Zkc.IR.Executable.Observations
import all Zkc.IR.Executable.Program
import all Zkc.IR.Executable.Reading
import all Zkc.IR.Executable.Refusal
import all Zkc.IR.Executable.Relation
import all Zkc.IR.Executable.StaticBudgetRejection
import all Zkc.IR.Executable.StaticSourceTransport
import all Zkc.Protocol.Library.Schnorr
import all Zkc.Verification.Installations.Schnorr.Common
import all Zkc.Program.Semantics.ExactRefinement
import all Zkc.Program.Execution
import all Zkc.Program.Interaction
import all Zkc.Program.Interpretation
import all Zkc.Program.MonadExecution
import all Zkc.Program.Semantics.StateInterpretation
import all Zkc.Program.Semantics.Yields
import all Zkc.IR.Source.Common.Scalar
import all Zkc.IR.Source.Common.Vocabulary
import all Zkc.Program.Source.Component
import all Zkc.Program.Source.ComponentCongruence
import all Zkc.Program.Region.Context
import all Zkc.Program.Source.ContextDecoding
import all Zkc.Program.Region.Operations
import all Zkc.Program.Source.Decidable
import all Zkc.Program.Source.Finite
import all Zkc.Program.Source.Format
import all Zkc.Program.Source.Interpretation
import all Zkc.Program.Source.KernelRfl
import all Zkc.Program.Source.Mathematical
import all Zkc.Program.Source.Mathematical.Projection
import all Zkc.Program.Source.Participant
import all Zkc.Program.Source.Program
import all Zkc.Program.Source.Region
import all Zkc.Program.Source.RegionCongruence
import all Zkc.Program.Source.RegionDecoding
import all Zkc.Program.Source.RegionInterpretation
import all Zkc.Program.Source.RoleFamily
import all Zkc.Program.Source.ScalarRegion
import all Zkc.Program.Region.Basic
import all Zkc.IR.Source.Structured.Admission
import all Zkc.IR.Source.Structured.Algebra
import all Zkc.IR.Source.Structured.ApplicationMetadata
import all Zkc.IR.Source.Structured.Association
import all Zkc.IR.Source.Structured.Availability
import all Zkc.IR.Source.Structured.Catalogue
import all Zkc.IR.Source.Structured.Checked
import all Zkc.IR.Source.Structured.CheckedData
import all Zkc.IR.Source.Structured.ClosedProfile
import all Zkc.IR.Source.Structured.CommonAdapter
import all Zkc.IR.Source.Structured.Component
import all Zkc.IR.Source.Structured.ComponentLinking
import all Zkc.IR.Source.Structured.ContractAdmission
import all Zkc.IR.Source.Structured.DomainComponent
import all Zkc.IR.Source.Structured.DomainEvaluation
import all Zkc.IR.Source.Structured.DomainInterpretation
import all Zkc.IR.Source.Structured.DomainModels
import all Zkc.IR.Source.Structured.DomainParticipant
import all Zkc.IR.Source.Structured.DomainParticipantInterpretation
import all Zkc.IR.Source.Structured.Evaluation
import all Zkc.IR.Source.Structured.Format
import all Zkc.IR.Source.Structured.Formation
import all Zkc.IR.Source.Structured.Frame
import all Zkc.IR.Source.Structured.HelperSources
import all Zkc.IR.Source.Structured.Import
import all Zkc.IR.Source.Structured.Interpretation
import all Zkc.IR.Source.Structured.IterationObservations
import all Zkc.IR.Source.Structured.Laws
import all Zkc.IR.Source.Structured.Limits
import all Zkc.IR.Source.Structured.Linking
import all Zkc.IR.Source.Structured.MapEvaluation
import all Zkc.IR.Source.Structured.MapLaws
import all Zkc.IR.Source.Structured.Meaning
import all Zkc.IR.Source.Structured.NaturalPowerOfTwo
import all Zkc.IR.Source.Structured.Occurrence
import all Zkc.IR.Source.Structured.OpenAdmission
import all Zkc.IR.Source.Structured.OpenLaws
import all Zkc.IR.Source.Structured.OpenMeaning
import all Zkc.IR.Source.Structured.Operations
import all Zkc.IR.Source.Structured.Origin
import all Zkc.IR.Source.Structured.OutputSelection
import all Zkc.IR.Source.Structured.Participant
import all Zkc.IR.Source.Structured.PolynomialValue
import all Zkc.IR.Source.Structured.Numerical
import all Zkc.IR.Source.Structured.NumericalCapabilities
import all Zkc.IR.Source.Structured.NumericalEvaluation
import all Zkc.IR.Source.Structured.NumericalLaws
import all Zkc.IR.Source.Structured.PreparationAdmission
import all Zkc.IR.Source.Structured.PrimitiveEvaluation
import all Zkc.IR.Source.Structured.Primitives
import all Zkc.IR.Source.Structured.ProtocolAdmission
import all Zkc.IR.Source.Structured.ProtocolContext
import all Zkc.IR.Source.Structured.ProtocolLinking
import all Zkc.IR.Source.Structured.ProtocolOperations
import all Zkc.IR.Source.Structured.ProtocolScopes
import all Zkc.IR.Source.Structured.ProtocolSignature
import all Zkc.IR.Source.Structured.ProtocolTable
import all Zkc.IR.Source.Structured.Provenance
import all Zkc.IR.Source.Structured.Repeat
import all Zkc.IR.Source.Structured.RepeatAdmission
import all Zkc.IR.Source.Structured.Table
import all Zkc.IR.Source.Structured.UnitViews
import all Zkc.IR.Source.Structured.Vocabulary
import all Zkc.Program.Specification
import all Zkc.Program.Transcript.Interface
import all Zkc.Applications.IR.Construction.DeferredRounds
import all Zkc.Applications.IR.Construction.DeferredRoundsData
import all Zkc.Applications.IR.Construction.DeferredRoundsParticipant
import all Zkc.Applications.IR.Construction.Generated.SchnorrRandomizedPair
import all Zkc.Applications.IR.Construction.SchnorrArtifact
import all Zkc.Applications.IR.Construction.SchnorrDomainConnection
import all Zkc.Applications.IR.Construction.SchnorrProof
import all Zkc.Applications.IR.Construction.SchnorrProofBodies
import all Zkc.Applications.IR.Construction.SchnorrProofData
import all Zkc.Applications.IR.Construction.SchnorrProofModel
import all Zkc.Applications.IR.Construction.SchnorrProofParticipant
import all Zkc.Applications.IR.Executable.DeferredRounds
import all Zkc.Applications.IR.Executable.DeferredRoundsDomainNormalization
import all Zkc.Applications.IR.Executable.DeferredRoundsFacts
import all Zkc.Applications.IR.Executable.DeferredRoundsProgramData
import all Zkc.Applications.IR.Executable.SchnorrProof
import all Zkc.Applications.IR.Executable.SchnorrProofFacts
import all Zkc.Applications.IR.Executable.SchnorrProofProgramData
import all Zkc.Applications.IR.NativePrograms.Schnorr
import all Zkc.Applications.IR.NativePrograms.SchnorrData
import all Zkc.Applications.IR.Structured.Generated.Constructed.SchnorrRandomizedValidator
import all Zkc.Applications.IR.Structured.Generated.Bindings.SchnorrRandomizedInputs
import all Zkc.IR.Construction.ConnectionActionCoverage
import all Zkc.IR.Construction.ConnectionActionSupport
import all Zkc.IR.Construction.ConnectionActions
import all Zkc.IR.Construction.ConnectionAdmission
import all Zkc.IR.Construction.ConnectionApplicationCoverageFrame
import all Zkc.IR.Construction.ConnectionApplicationFrame
import all Zkc.IR.Construction.ConnectionApplications
import all Zkc.IR.Construction.ConnectionCalculations
import all Zkc.IR.Construction.ConnectionCertificate
import all Zkc.IR.Construction.ConnectionCertificateAdmission
import all Zkc.IR.Construction.ConnectionComputation
import all Zkc.IR.Construction.ConnectionContext
import all Zkc.IR.Construction.ConnectionCoordinates
import all Zkc.IR.Construction.ConnectionFrame
import all Zkc.IR.Construction.ConnectionHelperCalculation
import all Zkc.IR.Construction.ConnectionHelperProjection
import all Zkc.IR.Construction.ConnectionHelpers
import all Zkc.IR.Construction.ConnectionInputFrames
import all Zkc.IR.Construction.ConnectionInputLayout
import all Zkc.IR.Construction.ConnectionInputSchema
import all Zkc.IR.Construction.ConnectionInputs
import all Zkc.IR.Construction.ConnectionInstallation
import all Zkc.IR.Construction.ConnectionLayout
import all Zkc.IR.Construction.ConnectionLibrary
import all Zkc.IR.Construction.ConnectionLoopFrames
import all Zkc.IR.Construction.ConnectionLoops
import all Zkc.IR.Construction.ConnectionMasking
import all Zkc.IR.Construction.ConnectionMathApplication
import all Zkc.IR.Construction.ConnectionMathFrames
import all Zkc.IR.Construction.ConnectionMathRegion
import all Zkc.IR.Construction.ConnectionMathRegionSoundness
import all Zkc.IR.Construction.ConnectionMathSimulation
import all Zkc.IR.Construction.ConnectionObservationPrefix
import all Zkc.IR.Construction.ConnectionObservations
import all Zkc.IR.Construction.ConnectionOrigins
import all Zkc.IR.Construction.ConnectionOutputSelection
import all Zkc.IR.Construction.ConnectionOutputs
import all Zkc.IR.Construction.ConnectionPresence
import all Zkc.IR.Construction.ConnectionProjectedContinuation
import all Zkc.IR.Construction.ConnectionReturnProjection
import all Zkc.IR.Construction.ConnectionProjectedFrames
import all Zkc.IR.Construction.ConnectionProjectedLoops
import all Zkc.IR.Construction.ConnectionRepeatSupport
import all Zkc.IR.Construction.ConnectionRoot
import all Zkc.IR.Construction.ConnectionRootCertificate
import all Zkc.IR.Construction.ConnectionRootInputs
import all Zkc.IR.Construction.ConnectionRootRoutes
import all Zkc.IR.Construction.ConnectionRouteCoverage
import all Zkc.IR.Construction.ConnectionRouteCoverageFrames
import all Zkc.IR.Construction.ConnectionRouteCoverageLoops
import all Zkc.IR.Construction.ConnectionRouteCoverageRoot
import all Zkc.IR.Construction.ConnectionRouteCoverageSupport
import all Zkc.IR.Construction.ConnectionRouting
import all Zkc.IR.Construction.ConnectionStaticRoutes
import all Zkc.IR.Construction.ConnectionSubstitution
import all Zkc.IR.Construction.ConnectionTargetExtent
import all Zkc.IR.Construction.ConnectionTargetPrefix
import all Zkc.IR.Construction.ConnectionTranscript
import all Zkc.IR.Construction.OriginalABI
import all Zkc.IR.Construction.OriginalEffects
import all Zkc.IR.Construction.OriginalFrameRelations
import all Zkc.IR.Construction.OriginalHeadReduction
import all Zkc.IR.Construction.OriginalHelperEncoding
import all Zkc.IR.Construction.OriginalHelpers
import all Zkc.IR.Construction.OriginalInputs
import all Zkc.IR.Construction.OriginalLoop
import all Zkc.IR.Construction.OriginalParticipant
import all Zkc.IR.Construction.PairAcceptance
import all Zkc.IR.Construction.ScalarConnection
import all Zkc.IR.Construction.SourceConnection
import all Zkc.IR.Construction.Uniform.LoopedSourceProcess
import all Zkc.IR.Construction.Uniform.ScalarFragment
import all Zkc.IR.Construction.Uniform.ScalarHandles
import all Zkc.IR.Construction.Uniform.ScalarObservation
import all Zkc.IR.Construction.Uniform.ScalarPresentation
import all Zkc.IR.Construction.Uniform.ScalarProjection
import all Zkc.IR.Construction.Uniform.ScalarSupport
import all Zkc.IR.Construction.Uniform.ScalarSupportProposer
import all Zkc.Program.Polynomial.BooleanCube
import all Zkc.Program.Polynomial.Coordinates
import all Zkc.Program.Polynomial.Multilinear
import all Zkc.Program.Polynomial.Multilinear.ListRestriction
import all Zkc.Program.Polynomial.Multilinear.Prefix
import all Zkc.Program.Polynomial.Multilinear.Restriction
import all Zkc.Program.Polynomial.Quadratic
import all Zkc.Program.Semantics.OperationSupport
import all Zkc.Program.Source.DenotationLaws
import all Zkc.Program.Source.OperationSupport
import all Zkc.IR.Source.Structured.CollectEvaluation
import all Zkc.IR.Source.Structured.ComponentClosure
import all Zkc.IR.Source.Structured.ComponentDeclarations
import all Zkc.IR.Source.Structured.DomainFrame
import all Zkc.IR.Source.Structured.DomainLinking
import all Zkc.IR.Source.Structured.DomainProtocolLinking
import all Zkc.IR.Source.Structured.FiniteDomains
import all Zkc.IR.Source.Structured.InputVisibility
import all Zkc.IR.Source.Structured.NormalForm.Denote
import all Zkc.IR.Source.Structured.NormalForm.Normalize
import all Zkc.IR.Source.Structured.NormalForm.Observation
import all Zkc.IR.Source.Structured.NormalForm.Soundness
import all Zkc.IR.Source.Structured.NormalForm.Syntax
import all Zkc.Applications.IR.Structured.Generated.Connections.SchnorrRandomized
import all Zkc.Applications.IR.Structured.Generated.Constructed.SchnorrRandomizedProducer
import all Zkc.Tools.IR.ConstructionBindings.Alignment
import all Zkc.Tools.IR.ConstructionBindings.Inputs
import all Zkc.Tools.IR.ConstructionBindings.LibraryBuilder
import all Zkc.Tools.IR.ConstructionBindings.LibraryPlan
import all Zkc.Tools.IR.ConstructionBindings.Readback
import all Zkc.Tools.IR.ConstructionBindings.Root
import all Zkc.Tools.IR.ConstructionBindings.Syntax
import all Zkc.IR.Construction.ConnectionServiceCoverage
import all Zkc.IR.Construction.ConnectionServiceRequests
import all Zkc.IR.Construction.ConnectionServiceRoutes
import all Zkc.IR.Construction.ConnectionTargetPlacement
import all Zkc.IR.Construction.ServiceConnection
import all Zkc.IR.Construction.ServiceRequests
import all Zkc.Program.Source.LogicalFormat
import all Zkc.Program.Source.RegionDerivation
import all Zkc.IR.Source.Structured.Addresses
import all Zkc.IR.Source.Structured.Bindings.Assembly
import all Zkc.IR.Source.Structured.Bindings.Component
import all Zkc.IR.Source.Structured.CatalogueEnvironment
import all Zkc.IR.Source.Structured.CustodyAdmission
import all Zkc.IR.Source.Structured.DomainLaws
import all Zkc.IR.Source.Structured.IndexWords
import all Zkc.IR.Source.Structured.InstalledCatalogue
import all Zkc.IR.Source.Structured.NormalForm.Presentation
import all Zkc.IR.Source.Structured.NormalForm.Sites
import all Zkc.IR.Source.Structured.OracleAdmission
import all Zkc.IR.Source.Structured.OracleBody
import all Zkc.IR.Source.Structured.OracleOperations
import all Zkc.IR.Source.Structured.OracleProtocolAdmission
import all Zkc.IR.Source.Structured.OracleValues
import all Zkc.IR.Source.Structured.ServiceAdmission
import all Zkc.IR.Source.Structured.ServiceExecution
import all Zkc.IR.Source.Structured.ServiceOperations
import all Zkc.IR.Source.Structured.SourceDeclarations
import all Zkc.IR.Source.Structured.SourcePlacementShape
public import Lean

/-! Full type/body and axiom audit. Missing dependencies fail. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := [``Zkc.Executable.StaticSourceTransport.readback_append_message,
    ``Zkc.Executable.StaticSourceTransport.readback_append_challenge,
    ``Zkc.Executable.StaticSourceTransport.sourceView_readable,
    ``Zkc.Executable.StaticSourceTransport.sourceView_keys,
    ``Zkc.Executable.ByteParticipantTransport.scalarVerdict,
    ``Zkc.Executable.ByteParticipantTransport.scalarSelected,
    ``Zkc.Executable.ByteParticipantTransport.scalarSelection,
    ``Zkc.Executable.ByteParticipantTransport.observedVerdict,
    ``Zkc.Executable.ByteParticipantTransport.observedVerdict_observation,
    ``Zkc.Executable.ByteParticipantTransport.byteAcceptance_selection,
    ``Zkc.Executable.ByteParticipantTransport.selected,
    ``Zkc.Executable.ByteParticipantTransport.nominalAcceptance_selected,
    ``Zkc.Executable.ByteParticipantTransport.run_nominalAcceptance,
    ``Zkc.Executable.ByteParticipantTransport.run_observe,
    ``Zkc.Executable.ByteParticipantTransport.mapOutcome_observation,
    ``Zkc.Executable.ByteParticipantTransport.readback_source_return,
    ``Zkc.Executable.ByteParticipantTransport.source_observation,
    ``Zkc.Executable.ByteParticipantTransport.run_map_yields,
    ``Zkc.Executable.ByteParticipantTransport.byteAcceptance_readable,
    ``Zkc.Executable.DomainVM.metered_short_maps,
    ``Zkc.Executable.DomainVM.checked_validate_rejects_static,
    ``ZkcExamples.Executable.SchnorrProof.prepared,
    ``ZkcExamples.Executable.SchnorrProof.helpersSorted,
    ``ZkcExamples.Executable.SchnorrProof.data,
    ``ZkcExamples.Executable.SchnorrProof.nominalData,
    ``ZkcExamples.Executable.SchnorrProof.embedded,
    ``ZkcExamples.Executable.SchnorrProof.native_prepared,
    ``ZkcExamples.Executable.SchnorrProof.nativeFinal,
    ``ZkcExamples.Executable.SchnorrProof.native_checked,
    ``ZkcExamples.Executable.SchnorrProof.schedule_instructions,
    ``ZkcExamples.Executable.SchnorrProof.schedule_returned,
    ``ZkcExamples.Executable.SchnorrProof.return_schema,
    ``ZkcExamples.Executable.SchnorrProof.schedule_source,
    ``ZkcExamples.Executable.SchnorrProof.schedule_keys,
    ``ZkcExamples.Executable.SchnorrProof.acceptance_selection,
    ``ZkcExamples.Executable.SchnorrProof.executable_observation,
    ``ZkcExamples.Executable.SchnorrProof.executable_transform,
    ``ZkcExamples.Executable.SchnorrProof.domain_prunes,
    ``ZkcExamples.Executable.SchnorrProof.executable_validate,
    ``ZkcExamples.Executable.SchnorrProof.executable_rejects,
    ``ZkcExamples.Executable.DeferredRounds.rescheduled,
    ``ZkcExamples.Executable.DeferredRounds.lowered_reading,
    ``ZkcExamples.Executable.DeferredRounds.nativeFinal,
    ``ZkcExamples.Executable.DeferredRounds.native_checked,
    ``ZkcExamples.Executable.DeferredRounds.return_schema,
    ``ZkcExamples.Executable.DeferredRounds.prepared,
    ``ZkcExamples.Executable.DeferredRounds.nominalData,
    ``ZkcExamples.Executable.DeferredRounds.embedded,
    ``ZkcExamples.Executable.DeferredRounds.schedule_normalized,
    ``ZkcExamples.Executable.DeferredRounds.readable_returns,
    ``ZkcExamples.Executable.DeferredRounds.canonical_acceptance,
    ``ZkcExamples.Executable.DeferredRounds.participant_observation,
    ``ZkcExamples.Executable.DeferredRounds.executable_observation,
    ``ZkcExamples.Executable.DeferredRounds.executable_prunes,
    ``ZkcExamples.Executable.DeferredRounds.executable_validate,
    ``ZkcExamples.Executable.DeferredRounds.executable_rejects,
    ``Tests.NativeByteConsumers.codec,
    ``Tests.NativeByteConsumers.challenge,
    ``Tests.NativeByteConsumers.binding,
    ``Tests.NativeByteConsumers.body,
    ``Tests.NativeByteConsumers.bytes,
    ``Tests.NativeByteConsumers.schnorr,
    ``Tests.NativeByteConsumers.deferred,
    ``Tests.NativeByteConsumers.schnorr_threshold,
    ``Tests.NativeByteConsumers.schnorr_short_keeps_query,
    ``Tests.NativeByteConsumers.schnorr_bad_header,
    ``Tests.NativeByteConsumers.schnorr_unread_refuses,
    ``Tests.NativeByteConsumers.deferred_threshold,
    ``Tests.NativeByteConsumers.deferred_short_keeps_queries,
    ``Tests.NativeByteConsumers.deferred_truncated_keeps_first_query,
    ``Tests.NativeByteConsumers.deferred_unread_refuses,
    ``Tests.NativeByteConsumers.wrongResponse,
    ``Tests.NativeByteConsumers.schnorrWrong,
    ``Tests.NativeByteConsumers.schnorr_wrong_nominal_response,
    ``Tests.NativeByteConsumers.deferred_strong_admission,
    ``Tests.NativeByteConsumers.arbitrary_origin_is_not_static,
    ``ZkcExamples.Executable.DeferredRounds.normalization_checked,
    ``ZkcExamples.Executable.DeferredRounds.normalized_schedule]
  let forbidden := [`Zkc.Construction.specK, `Zkc.Construction.specStep,
    `Zkc.Construction.idealK, `Zkc.Construction.idealStep,
    `Zkc.Construction.spec, `Zkc.Construction.ideal,
    `Zkc.Executable.meteredK, `Zkc.Executable.meteredIterate, `Zkc.Executable.meteredStep,
    `Zkc.Executable.metered, `Zkc.Construction.Uniform.compiled_selected]
  let mut pending := roots
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then throwError "native/Domain proof reaches retired interpreter: {name}"
    let some info := env.checked.get.find? name | throwError "missing dependency: {name}"
    if info.isUnsafe then throwError "native/Domain proof reaches unsafe declaration: {name}"
    let project := match env.getModuleIdxFor? name with
      | some index =>
        let owner := env.header.moduleNames[index.toNat]!.toString
        owner == "Zkc" || owner.startsWith "Zkc." || owner.startsWith "ZkcExamples." || owner.startsWith "Tests."
      | none => true
    if project then
      if info.isAxiom then throwError "project proof body unavailable: {name}"
    else continue
    let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
    pending := (info.type.getUsedConstants ++ values).toList ++ pending
  let mut axiomsUsed : Std.HashSet Name := {}
  for root in roots do
    for axiomName in ← collectAxioms root do
      axiomsUsed := axiomsUsed.insert axiomName
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "nonstandard axiom: {root} depends on {axiomName}"
  logInfo m!"NATIVE-BYTE-CONSUMERS-DEPENDENCIES-PASS roots={roots.length} dependencies={seen.size}"

  logInfo m!"NATIVE-BYTE-CONSUMERS-AXIOMS {axiomsUsed.toList}"
