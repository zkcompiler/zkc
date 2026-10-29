module
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.Source.Structured.RelationChecking
import all Zkc.Source.Structured.FiniteDomains
import all Zkc.Source.Structured.CollectionReferenceLaws
import all Zkc.Source.Structured.ReferenceLaws
import all Zkc.Source.Structured.ReferenceLibrary
import all Zkc.Source.Structured.MultilinearBodies
import all Zkc.Source.Structured.MultilinearReference
import all Zkc.Source.Structured.MultilinearAdmissionReference
import all Zkc.Source.Structured.CollectEvaluation
import all Zkc.Source.Structured.CollectLaws
import all ZkcExamples.Structured.MultilinearCollectBodies
import all ZkcExamples.Structured.MultilinearCollectLaws
import all ZkcExamples.Structured.MultilinearPrefixBodies
import all ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
import all Tests.DomainNativeScope
import all Zkc.Algebra.RingExpression.Basic
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
import all Zkc.Construction.SourceDelivery
import all Zkc.Construction.SourceOccurrences
import all Zkc.Construction.Structured
import all Zkc.Construction.Uniform.DomainExecution
import all Zkc.Construction.Uniform.DomainHandler
import all Zkc.Construction.Uniform.DomainProperties
import all Zkc.Executable.Cleanup
import all Zkc.Executable.Code
import all Zkc.Executable.Decoding
import all Zkc.Executable.DomainByteLaws
import all Zkc.Executable.DomainCompleteness
import all Zkc.Executable.DomainHelpers
import all Zkc.Executable.DomainLowering
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
import all Zkc.Executable.DomainOrigins
import all Zkc.Executable.DomainProcesses
import all Zkc.Executable.DomainSchema
import all Zkc.Executable.DomainSoundness
import all Zkc.Executable.Evaluation
import all Zkc.Executable.Execution
import all Zkc.Executable.Framing
import all Zkc.Executable.HelperSoundness
import all Zkc.Executable.Helpers
import all Zkc.Executable.Installed
import all Zkc.Executable.NativeLaws
import all Zkc.Executable.DomainNormalizationCheck
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
import all Zkc.Protocols.Schnorr
import all Zkc.Protocols.Schnorr.Common
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
import all Zkc.Source.Common.Import
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
import all ZkcExamples.Construction.SchnorrArtifact
import all ZkcExamples.Construction.SchnorrProofBodies
import all ZkcExamples.Construction.SchnorrProofData
import all ZkcExamples.Construction.SchnorrProofModel
import all ZkcExamples.Construction.SchnorrProofParticipant
import all ZkcExamples.Construction.SumcheckArtifact
import all ZkcExamples.Construction.SumcheckProofParticipant
import all ZkcExamples.Executable.SchnorrProofProgramData
import all ZkcExamples.Executable.SumcheckHelpers
import all ZkcExamples.Executable.SumcheckProofProgramData
import all ZkcExamples.NativePrograms.Schnorr
import all ZkcExamples.NativePrograms.SchnorrData
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
import all ZkcExamples.Structured.SumcheckSourceViews
import all ZkcExamples.Structured.SumcheckUnitContracts
import all ZkcExamples.Structured.SumcheckVerifierBodies
import all ZkcExamples.Structured.SumcheckVerifierHelpers
public import Lean

/-! Dependency and axiom regression controls for direct native/Domain roots. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := [``Zkc.Executable.DomainVM.checkNativeLowering_preserves,
    ``Zkc.Executable.DomainVM.decodeProof_frames_local,
    ``Zkc.Executable.DomainVM.runK_frames_local,
    ``Zkc.Executable.execute_cleaned,
    ``Zkc.Executable.DomainVM.native_operation_metered,
    ``Zkc.Executable.DomainVM.native_localK_metered,
    ``Zkc.Executable.DomainVM.native_runK_metered,
    ``Zkc.Executable.DomainVM.checked_execute_metered,
    ``Zkc.Executable.DomainVM.checked_validate_metered,
    ``Zkc.Executable.DomainVM.checked_validate_prunes,
    ``Zkc.Executable.DomainVM.checked_execute_sufficient,
    ``Zkc.Executable.DomainVM.checked_execute_static,
    ``Zkc.Executable.DomainVM.checked_validate_sufficient,
    ``Tests.DomainNativeScope.schnorr_native_correspondence,
    ``Tests.DomainNativeScope.sumcheck_native_correspondence]
  let forbidden := [`Zkc.Construction.specK, `Zkc.Construction.specStep,
    `Zkc.Construction.idealK, `Zkc.Construction.idealStep,
    `Zkc.Construction.spec, `Zkc.Construction.ideal,
    `Zkc.Executable.meteredK, `Zkc.Executable.meteredIterate, `Zkc.Executable.meteredStep,
    `Zkc.Executable.metered, `Zkc.Construction.Uniform.compiled_selected]
  -- Namespace is not ownership: PIR declarations live in Zkc.Semantics.
  let project := fun (name : Name) =>
    match env.getModuleIdxFor? name with
    | some index =>
      let owner := env.header.moduleNames[index.toNat]!.toString
      owner == "Zkc" || owner.startsWith "Zkc." || owner.startsWith "ZkcExamples." ||
        owner.startsWith "Tests."
    | none => true -- A found declaration without an imported module is local.
  unless project ``PIR.Process.bind do
    throwError "project ownership omitted the Process implementation"
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
    if project name then
      if info.isAxiom then throwError "project proof body unavailable: {name}"
    else continue
    let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
    pending := (info.type.getUsedConstants ++ values).toList ++ pending
  for root in roots do
    for axiomName in ← collectAxioms root do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "nonstandard axiom: {root} depends on {axiomName}"
  logInfo m!"NATIVE-DOMAIN-DEPENDENCIES-PASS roots={roots.length} dependencies={seen.size}"

#print axioms Zkc.Executable.DomainVM.native_operation_metered
#print axioms Zkc.Executable.DomainVM.native_localK_metered
#print axioms Zkc.Executable.DomainVM.native_runK_metered
#print axioms Zkc.Executable.DomainVM.checked_execute_metered
#print axioms Zkc.Executable.DomainVM.checked_validate_metered
#print axioms Zkc.Executable.DomainVM.checked_validate_prunes
#print axioms Zkc.Executable.DomainVM.checked_execute_static
#print axioms Zkc.Executable.DomainVM.checked_validate_sufficient
#print axioms Zkc.Executable.DomainVM.checked_execute_sufficient
#print axioms Tests.DomainNativeScope.schnorr_native_correspondence
#print axioms Tests.DomainNativeScope.sumcheck_native_correspondence
#print axioms Zkc.Executable.execute_cleaned

#print axioms Zkc.Executable.DomainVM.checkNativeLowering_preserves
#print axioms Zkc.Executable.DomainVM.decodeProof_frames_local
#print axioms Zkc.Executable.DomainVM.runK_frames_local
