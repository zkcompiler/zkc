module
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.Source.Structured.RelationChecking
import all Tests.NativeByteConsumers
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
import all Zkc.Construction.Uniform.DomainProperties
import all Zkc.Construction.Uniform.SourceProcess
import all Zkc.Executable.ByteParticipantTransport
import all Zkc.Executable.Code
import all Zkc.Executable.Decoding
import all Zkc.Executable.DomainAnchorSemantics
import all Zkc.Executable.DomainByteLaws
import all Zkc.Executable.DomainCompleteness
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
import all Zkc.Executable.DomainTermSemantics
import all Zkc.Executable.DomainVerifierTransport
import all Zkc.Executable.Evaluation
import all Zkc.Executable.Execution
import all Zkc.Executable.Framing
import all Zkc.Executable.HelperSoundness
import all Zkc.Executable.Helpers
import all Zkc.Executable.Installed
import all Zkc.Executable.NativeLaws
import all Zkc.Executable.HelperSchemas
import all Zkc.Executable.Numerical
import all Zkc.Executable.Observations
import all Zkc.Executable.Program
import all Zkc.Executable.Reading
import all Zkc.Executable.Refusal
import all Zkc.Executable.Relation
import all Zkc.Executable.StaticBudgetRejection
import all Zkc.Executable.StaticSourceTransport
import all Zkc.Protocols.Schnorr
import all Zkc.Protocols.Schnorr.Common
import all Zkc.Semantics.ExactRefinement
import all Zkc.Semantics.Execution
import all Zkc.Semantics.Interaction
import all Zkc.Semantics.Interpretation
import all Zkc.Semantics.MonadExecution
import all Zkc.Semantics.StateInterpretation
import all Zkc.Semantics.Yields
import all Zkc.Source.Common
import all Zkc.Source.Common.Import
import all Zkc.Source.Common.Scalar
import all Zkc.Source.Common.Vocabulary
import all Zkc.Source.Component
import all Zkc.Source.ComponentCongruence
import all Zkc.Source.Context
import all Zkc.Source.ContextDecoding
import all Zkc.Source.ContextOperations
import all Zkc.Source.Decidable
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
import all Zkc.Source.RegionDecoding
import all Zkc.Source.RegionInterpretation
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
import all Zkc.Source.Structured.Table
import all Zkc.Source.Structured.UnitViews
import all Zkc.Source.Structured.Vocabulary
import all Zkc.Specification
import all Zkc.Transcript.Interface
import all ZkcExamples.Construction.DeferredRounds
import all ZkcExamples.Construction.DeferredRoundsData
import all ZkcExamples.Construction.DeferredRoundsParticipant
import all ZkcExamples.Construction.Generated.SchnorrRandomizedPair
import all ZkcExamples.Construction.SchnorrArtifact
import all ZkcExamples.Construction.SchnorrDomainConnection
import all ZkcExamples.Construction.SchnorrProof
import all ZkcExamples.Construction.SchnorrProofBodies
import all ZkcExamples.Construction.SchnorrProofData
import all ZkcExamples.Construction.SchnorrProofModel
import all ZkcExamples.Construction.SchnorrProofParticipant
import all ZkcExamples.Executable.DeferredRounds
import all ZkcExamples.Executable.DeferredRoundsDomainNormalization
import all ZkcExamples.Executable.DeferredRoundsFacts
import all ZkcExamples.Executable.DeferredRoundsProgramData
import all ZkcExamples.Executable.SchnorrProof
import all ZkcExamples.Executable.SchnorrProofFacts
import all ZkcExamples.Executable.SchnorrProofProgramData
import all ZkcExamples.NativePrograms.Schnorr
import all ZkcExamples.NativePrograms.SchnorrData
import all ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator
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
