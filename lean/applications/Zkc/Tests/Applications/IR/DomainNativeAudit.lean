module
import all Zkc.IR.Source.Structured.DomainContract
import all Zkc.IR.Source.Structured.DomainLinking
import all Zkc.IR.Source.Structured.DomainFrame
import all Zkc.IR.Source.Structured.CollectionRepresentation
import all Zkc.Protocol.Library.Sumcheck.Multilinear.Fold
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.IR.Source.Structured.RelationChecking
import all Zkc.IR.Source.Structured.FiniteDomains
import all Zkc.IR.Source.Structured.CollectionReferenceLaws
import all Zkc.IR.Source.Structured.CollectionReference
import all Zkc.IR.Source.Structured.ReferenceLaws
import all Zkc.Program.Semantics.ReturnView
import all Zkc.IR.Source.Structured.MultilinearReferenceViews
import all Zkc.IR.Source.Structured.ReferenceLibrary
import all Zkc.IR.Source.Structured.MultilinearBodies
import all Zkc.IR.Source.Structured.MultilinearReference
import all Zkc.IR.Source.Structured.MultilinearAdmissionReference
import all Zkc.IR.Source.Structured.CollectEvaluation
import all Zkc.IR.Source.Structured.CollectLaws
import all Zkc.Verification.Installations.Multilinear.Source.CollectBodies
import all Zkc.Verification.Installations.Multilinear.Source.CollectLaws
import all Zkc.Verification.Installations.Multilinear.Source.PrefixBodies
import all Zkc.Verification.Installations.Sumcheck.Source.DomainHelpers
import all Zkc.Verification.Installations.Sumcheck.Source.MathematicalHelpers
import all Zkc.Protocol.Library.Sumcheck.Source.Representation
import all Zkc.Tests.Applications.IR.DomainNativeScope
import all Zkc.Program.Algebra.RingExpression.Basic
import all Zkc.IR.Construction.Binding
import all Zkc.IR.Construction.Compiled
import all Zkc.IR.Construction.Context
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
import all Zkc.IR.Construction.SourceDelivery
import all Zkc.IR.Construction.SourceOccurrences
import all Zkc.IR.Construction.Structured
import all Zkc.IR.Construction.Uniform.DomainExecution
import all Zkc.IR.Construction.Uniform.DomainHandler
import all Zkc.IR.Construction.Uniform.DomainProperties
import all Zkc.IR.Executable.Cleanup
import all Zkc.IR.Executable.Code
import all Zkc.IR.Executable.Decoding
import all Zkc.IR.Executable.DomainByteLaws
import all Zkc.IR.Executable.DomainCompleteness
import all Zkc.IR.Executable.DomainHelpers
import all Zkc.IR.Executable.DomainLowering
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
import all Zkc.IR.Executable.DomainOrigins
import all Zkc.IR.Executable.DomainProcesses
import all Zkc.IR.Executable.DomainSchema
import all Zkc.IR.Executable.DomainSoundness
import all Zkc.IR.Executable.Evaluation
import all Zkc.IR.Executable.Execution
import all Zkc.IR.Executable.Framing
import all Zkc.IR.Executable.HelperSoundness
import all Zkc.IR.Executable.Helpers
import all Zkc.IR.Executable.Installed
import all Zkc.IR.Executable.NativeLaws
import all Zkc.IR.Executable.DomainNormalizationCheck
import all Zkc.IR.Executable.Numerical
import all Zkc.IR.Executable.Observations
import all Zkc.IR.Executable.Program
import all Zkc.IR.Executable.Reading
import all Zkc.IR.Executable.Refusal
import all Zkc.IR.Executable.Relation
import all Zkc.Program.Polynomial.BooleanCube
import all Zkc.Program.Polynomial.Coordinates
import all Zkc.Program.Polynomial.Multilinear
import all Zkc.Program.Polynomial.Multilinear.ListRestriction
import all Zkc.Program.Polynomial.Multilinear.Marginal
import all Zkc.Program.Polynomial.Multilinear.Prefix
import all Zkc.Program.Polynomial.Multilinear.Restriction
import all Zkc.Program.Polynomial.Quadratic
import all Zkc.Protocol.Library.Schnorr
import all Zkc.Verification.Installations.Schnorr.Common
import all Zkc.Protocol.Library.Sumcheck.Multilinear.Reduction
import all Zkc.Protocol.Library.Sumcheck.Multilinear.Round
import all Zkc.Program.Semantics.Boundary
import all Zkc.Program.Semantics.ExactRefinement
import all Zkc.Program.Execution
import all Zkc.Program.Semantics.ExecutionPath
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
import all Zkc.Program.Source.DenotationLaws
import all Zkc.Program.Source.DerivationLaws
import all Zkc.Program.Source.DeriveRegion
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
import all Zkc.Program.Source.RegionContracts
import all Zkc.Program.Source.RegionDecoding
import all Zkc.Program.Source.RegionDerivation
import all Zkc.Program.Source.RegionInterpretation
import all Zkc.Program.Source.RegionTotality
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
import all Zkc.IR.Source.Structured.ContractBinding
import all Zkc.IR.Source.Structured.ContractBoundary
import all Zkc.IR.Source.Structured.ContractCalls
import all Zkc.IR.Source.Structured.ContractComposition
import all Zkc.IR.Source.Structured.ContractInstantiation
import all Zkc.IR.Source.Structured.DerivationRules
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
import all Zkc.IR.Source.Structured.NormalForm.Denote
import all Zkc.IR.Source.Structured.NormalForm.Normalize
import all Zkc.IR.Source.Structured.NormalForm.Presentation
import all Zkc.IR.Source.Structured.NormalForm.Soundness
import all Zkc.IR.Source.Structured.NormalForm.Syntax
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
import all Zkc.IR.Source.Structured.PrimitiveLaws
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
import all Zkc.IR.Source.Structured.RepeatLaws
import all Zkc.IR.Source.Structured.Table
import all Zkc.IR.Source.Structured.UnitViews
import all Zkc.IR.Source.Structured.Vocabulary
import all Zkc.Program.Specification
import all Zkc.Program.Transcript.Interface
import all Zkc.Applications.IR.Construction.SchnorrArtifact
import all Zkc.Applications.IR.Construction.SchnorrProofBodies
import all Zkc.Applications.IR.Construction.SchnorrProofData
import all Zkc.Applications.IR.Construction.SchnorrProofModel
import all Zkc.Applications.IR.Construction.SchnorrProofParticipant
import all Zkc.Applications.IR.Construction.SumcheckArtifact
import all Zkc.Applications.IR.Construction.SumcheckProofParticipant
import all Zkc.Applications.IR.Executable.SchnorrProofProgramData
import all Zkc.Applications.IR.Executable.SumcheckHelpers
import all Zkc.Applications.IR.Executable.SumcheckProofProgramData
import all Zkc.Applications.IR.NativePrograms.Schnorr
import all Zkc.Applications.IR.NativePrograms.SchnorrData
import all Zkc.Verification.Installations.Multilinear.Source.MapFirstBodies
import all Zkc.Verification.Installations.Multilinear.Source.MapFirstContracts
import all Zkc.Verification.Installations.Multilinear.Source.MapFirstLaws
import all Zkc.Verification.Installations.Multilinear.Source.MapPrefixBodies
import all Zkc.Verification.Installations.Multilinear.Source.MapPrefixContracts
import all Zkc.Verification.Installations.Multilinear.Source.MapPrefixLaws
import all Zkc.Verification.Installations.Multilinear.Source.MapProjectionContracts
import all Zkc.Verification.Installations.Multilinear.Source.MapSourceExpansions
import all Zkc.IR.Source.Structured.NormalForm.Steps
import all Zkc.Applications.IR.Structured.PrimitiveExpansions
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveExpansions
import all Zkc.Applications.IR.Structured.PrimitiveHalvesData
import all Zkc.Applications.IR.Structured.PrimitiveHalvesViews
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveHalvesBodies
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveLibrary
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveRows
import all Zkc.Applications.IR.Structured.PrimitiveSequenceData
import all Zkc.Applications.IR.Structured.PrimitiveSequenceViews
import all Zkc.Applications.IR.Structured.PrimitiveShapeData
import all Zkc.Applications.IR.Structured.PrimitiveShapeViews
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveShapeBodies
import all Zkc.Applications.IR.Structured.PrimitiveTableData
import all Zkc.Applications.IR.Structured.PrimitiveTableViews
import all Zkc.Verification.Installations.Multilinear.Source.PrimitiveTableBodies
import all Zkc.Verification.Installations.Sumcheck.Source.HelperBodies
import all Zkc.Verification.Installations.Sumcheck.Source.HelperBridge
import all Zkc.Verification.Installations.Sumcheck.Source.HelperExpansions
import all Zkc.Verification.Installations.Sumcheck.Source.HelperLaws
import all Zkc.Applications.IR.Structured.SumcheckRelationContract
import all Zkc.Verification.Installations.Sumcheck.Source.RoundLaws
import all Zkc.Verification.Installations.Sumcheck.Source.RoundNormalForms
import all Zkc.Applications.IR.Structured.SumcheckSourceAssociations
import all Zkc.Applications.IR.Structured.SumcheckSourceBodies
import all Zkc.Applications.IR.Structured.SumcheckSourceContracts
import all Zkc.Applications.IR.Structured.SumcheckSourceData
import all Zkc.Applications.IR.Structured.SumcheckSourceLaws
import all Zkc.Applications.IR.Structured.SumcheckSourceNormalForms
import all Zkc.Applications.IR.Structured.SumcheckSourceViews
import all Zkc.Verification.Installations.Sumcheck.Source.UnitContracts
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierBodies
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierHelpers
import all Zkc.IR.Construction.ServiceRequests
import all Zkc.Verification.Installations.Multilinear.Source.Bindings
import all Zkc.Verification.Installations.Sumcheck.Source.Checks
import all Zkc.Verification.Installations.Sumcheck.Source.Library
import all Zkc.Verification.Installations.Sumcheck.Source.PendingBodies
import all Zkc.Verification.Installations.Sumcheck.Source.PendingLaws
import all Zkc.Verification.Installations.Sumcheck.Source.PreludeNormalForms
import all Zkc.Verification.Installations.Sumcheck.Source.ProverLaws
import all Zkc.Verification.Installations.Sumcheck.Source.ProverProcess
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierLaws
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierProcess
import all Zkc.Program.Source.LogicalFormat
import all Zkc.IR.Source.Structured.Addresses
import all Zkc.IR.Source.Structured.Bindings.Assembly
import all Zkc.IR.Source.Structured.Bindings.Component
import all Zkc.IR.Source.Structured.Bindings.Selection
import all Zkc.IR.Source.Structured.BodyBindings
import all Zkc.IR.Source.Structured.CatalogueEnvironment
import all Zkc.IR.Source.Structured.ComponentDeclarations
import all Zkc.IR.Source.Structured.ContractApplication
import all Zkc.IR.Source.Structured.ContractExecution
import all Zkc.IR.Source.Structured.ContractMeaning
import all Zkc.IR.Source.Structured.ContractObligations
import all Zkc.IR.Source.Structured.CustodyAdmission
import all Zkc.IR.Source.Structured.DomainLaws
import all Zkc.IR.Source.Structured.DomainProtocolLinking
import all Zkc.IR.Source.Structured.IndexWords
import all Zkc.IR.Source.Structured.InputVisibility
import all Zkc.IR.Source.Structured.InstalledCatalogue
import all Zkc.IR.Source.Structured.LogicalContext
import all Zkc.IR.Source.Structured.LogicalInstantiation
import all Zkc.IR.Source.Structured.LogicalTranslation
import all Zkc.IR.Source.Structured.LoopPresentation
import all Zkc.IR.Source.Structured.NormalForm.Observation
import all Zkc.IR.Source.Structured.NormalForm.Sites
import all Zkc.IR.Source.Structured.OccurrencePresentation
import all Zkc.IR.Source.Structured.OpaqueRegistry
import all Zkc.IR.Source.Structured.OracleAdmission
import all Zkc.IR.Source.Structured.OracleBody
import all Zkc.IR.Source.Structured.OracleOperations
import all Zkc.IR.Source.Structured.OracleProtocolAdmission
import all Zkc.IR.Source.Structured.OracleValues
import all Zkc.IR.Source.Structured.PlainHelpers
import all Zkc.IR.Source.Structured.ProtocolPresentation
import all Zkc.IR.Source.Structured.ServiceAdmission
import all Zkc.IR.Source.Structured.ServiceExecution
import all Zkc.IR.Source.Structured.ServiceOperations
import all Zkc.IR.Source.Structured.SourceDeclarations
import all Zkc.IR.Source.Structured.SourcePlacementShape
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
