module
import all Zkc.IR.Source.Structured.DomainContract
import all Zkc.IR.Source.Structured.CollectionRepresentation
import all Zkc.IR.Source.Structured.Bindings.Assembly
import all Zkc.IR.Source.Structured.Bindings.Component
import all Zkc.IR.Source.Structured.Bindings.Selection
import all Zkc.IR.Source.Structured.LoopPresentation
import all Zkc.IR.Source.Structured.NormalForm.Sites
import all Zkc.IR.Source.Structured.OccurrencePresentation
import all Zkc.IR.Source.Structured.ProtocolPresentation
import all Zkc.Applications.IR.Structured.Generated.Scalar.SumcheckSource
import all Zkc.Applications.IR.Structured.Generated.Scalar.SumcheckSourceBindings
import all Zkc.Applications.IR.Structured.Generated.Scalar.SumcheckSourceBindingsCallbacks
import all Zkc.Applications.IR.Structured.Generated.Scalar.SumcheckSourceLibrary
import all Zkc.Tools.IR.ConstructionBindings.Alignment
import all Zkc.Tools.IR.ConstructionBindings.Inputs
import all Zkc.Tools.IR.ConstructionBindings.LibraryBuilder
import all Zkc.Tools.IR.ConstructionBindings.LibraryPlan
import all Zkc.Tools.IR.ConstructionBindings.Readback
import all Zkc.Tools.IR.ConstructionBindings.Root
import all Zkc.Tools.IR.ConstructionBindings.Syntax
import all Zkc.IR.Source.Structured.ReferenceLaws
import all Zkc.Program.Semantics.ReturnView
import all Zkc.IR.Source.Structured.MultilinearReferenceViews
import all Zkc.IR.Source.Structured.ReferenceLibrary
import all Zkc.IR.Source.Structured.MultilinearBodies
import all Zkc.IR.Source.Structured.MultilinearReference
import all Zkc.IR.Source.Structured.MultilinearAdmissionReference
-- Load stored private equality proofs for the strict dependency traversal.
import all Zkc.IR.Source.Structured.RelationChecking
import all Zkc.IR.Source.Structured.FiniteDomains
import all Zkc.IR.Source.Structured.CollectionReferenceLaws
import all Zkc.IR.Source.Structured.CollectionReference
import all Zkc.IR.Source.Structured.CollectEvaluation
import all Zkc.IR.Source.Structured.CollectLaws
import all Zkc.Verification.Installations.Multilinear.Source.CollectBodies
import all Zkc.Verification.Installations.Multilinear.Source.CollectLaws
import all Zkc.Verification.Installations.Multilinear.Source.PrefixBodies
import all Zkc.Verification.Installations.Sumcheck.Source.DomainHelpers
import all Zkc.Verification.Installations.Sumcheck.Source.MathematicalHelpers
import all Zkc.Protocol.Library.Sumcheck.Source.Representation

import all Zkc.Tests.Applications.IR.SumcheckNativeConsumer
import all Zkc.Program.Algebra.RingExpression.Basic
import all Zkc.IR.Construction.ArtifactBinding
import all Zkc.Tools.IR.ConstructionBindings.ArtifactBindingTactic
import all Zkc.IR.Construction.AuthoredPair
import all Zkc.IR.Construction.AuthoredPairProducer
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
import all Zkc.IR.Construction.ScalarVerifier
import all Zkc.IR.Construction.SourceDelivery
import all Zkc.IR.Construction.SourceOccurrences
import all Zkc.IR.Construction.Structured
import all Zkc.Tools.Program.ConstructionBindings.TransportReduction
import all Zkc.IR.Construction.Uniform.DomainExecution
import all Zkc.IR.Construction.Uniform.DomainHandler
import all Zkc.IR.Construction.Uniform.DomainIteration
import all Zkc.IR.Construction.Uniform.DomainProperties
import all Zkc.IR.Executable.Cleanup
import all Zkc.IR.Executable.Code
import all Zkc.IR.Executable.Decoding
import all Zkc.IR.Executable.DomainAnchorSemantics
import all Zkc.IR.Executable.DomainByteLaws
import all Zkc.IR.Executable.DomainCompleteness
import all Zkc.IR.Executable.DomainFitsRules
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
import all Zkc.IR.Executable.DomainSuccess
import all Zkc.IR.Executable.DomainSuccessRules
import all Zkc.IR.Executable.DomainTermSemantics
import all Zkc.IR.Executable.DomainVerifierTransport
import all Zkc.IR.Executable.Evaluation
import all Zkc.IR.Executable.Execution
import all Zkc.IR.Executable.Framing
import all Zkc.IR.Executable.HelperCosts
import all Zkc.IR.Executable.HelperSchemas
import all Zkc.IR.Executable.HelperSoundness
import all Zkc.IR.Executable.Helpers
import all Zkc.IR.Executable.Installed
import all Zkc.IR.Executable.NativeLaws
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
import all Zkc.Protocol.Library.Sumcheck.Multilinear.Fold
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
import all Zkc.IR.Source.Structured.PreparationAdmission
import all Zkc.IR.Source.Structured.PrimitiveEvaluation
import all Zkc.IR.Source.Structured.PrimitiveLaws
import all Zkc.IR.Source.Structured.Primitives
import all Zkc.IR.Source.Structured.PlainHelpers
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
import all Zkc.Applications.IR.Construction.Generated.SmallSumcheckPair
import all Zkc.Applications.IR.Construction.SumcheckArtifact
import all Zkc.Applications.IR.Construction.SumcheckProof
import all Zkc.Applications.IR.Construction.SumcheckProofParticipant
import all Zkc.Applications.IR.Construction.SumcheckSourceConnection
import all Zkc.Applications.IR.Executable.SumcheckCharges
import all Zkc.Applications.IR.Executable.SumcheckCompleteness
import all Zkc.Applications.IR.Executable.SumcheckDomainHonest
import all Zkc.Applications.IR.Executable.SumcheckFamily
import all Zkc.Applications.IR.Executable.SumcheckFamilyBudget
import all Zkc.Applications.IR.Executable.SumcheckFamilySource
import all Zkc.Applications.IR.Executable.SumcheckFamilyResources
import all Zkc.Applications.IR.Executable.SumcheckHelpers
import all Zkc.Applications.IR.Executable.SumcheckMessages
import all Zkc.Applications.IR.Executable.SumcheckMetadata
import all Zkc.Applications.IR.Executable.SumcheckProof
import all Zkc.Applications.IR.Executable.SumcheckProofFacts
import all Zkc.Applications.IR.Executable.SumcheckProofProgramData
import all Zkc.Applications.IR.Executable.SumcheckShape
import all Zkc.Applications.IR.Structured.Generated.Bindings.SmallSumcheckInputs
import all Zkc.Applications.IR.Structured.Generated.Constructed.SmallSumcheckValidator
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
import all Zkc.Verification.Installations.Sumcheck.Source.PendingLaws
import all Zkc.Verification.Installations.Sumcheck.Source.PreludeNormalForms
import all Zkc.Applications.IR.Structured.SumcheckRelationContract
import all Zkc.Verification.Installations.Sumcheck.Source.RoundLaws
import all Zkc.Verification.Installations.Sumcheck.Source.RoundNormalForms
import all Zkc.Applications.IR.Structured.SumcheckSourceAssociations
import all Zkc.Applications.IR.Structured.SumcheckSourceBodies
import all Zkc.Applications.IR.Structured.SumcheckSourceContracts
import all Zkc.Applications.IR.Structured.SumcheckSourceData
import all Zkc.Applications.IR.Structured.SumcheckSourceLaws
import all Zkc.Applications.IR.Structured.SumcheckSourceNormalForms
import all Zkc.Applications.IR.Structured.SumcheckSourceVerifier
import all Zkc.Applications.IR.Structured.SumcheckSourceViews
import all Zkc.Verification.Installations.Sumcheck.Source.UnitContracts
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierBodies
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierHelpers
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierLaws
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierPrelude
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierProcess
import all Zkc.Applications.IR.Structured.SumcheckVerifierTerminal
import all Zkc.Verification.Installations.Sumcheck.Source.VerifierTerminal
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
import all Zkc.IR.Construction.ConnectionFrameLookup
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
import all Zkc.IR.Construction.Uniform.ScalarCheckedBytes
import all Zkc.IR.Construction.Uniform.ScalarCheckedFrames
import all Zkc.IR.Construction.Uniform.ScalarFragment
import all Zkc.IR.Construction.Uniform.ScalarHandles
import all Zkc.IR.Construction.Uniform.ScalarObservation
import all Zkc.IR.Construction.Uniform.ScalarProjection
import all Zkc.IR.Construction.Uniform.ScalarSourceCost
import all Zkc.IR.Construction.Uniform.ScalarSupport
import all Zkc.IR.Construction.Uniform.ScalarSupportProposer
import all Zkc.IR.Construction.Uniform.SourceProcess
import all Zkc.Tools.IR.ConstructionBindings.ScalarConnection
import all Zkc.Program.Semantics.OperationSupport
import all Zkc.Program.Source.OperationSupport
import all Zkc.IR.Source.Structured.BodyBindings
import all Zkc.IR.Source.Structured.ComponentClosure
import all Zkc.IR.Source.Structured.ComponentDeclarations
import all Zkc.IR.Source.Structured.DomainFrame
import all Zkc.IR.Source.Structured.DomainLinking
import all Zkc.IR.Source.Structured.DomainProtocolLinking
import all Zkc.IR.Source.Structured.InputVisibility
import all Zkc.IR.Source.Structured.NormalForm.Observation
import all Zkc.Applications.IR.Executable.SumcheckCheckedRound
import all Zkc.Applications.IR.Executable.SumcheckSourceHonest
import all Zkc.Applications.IR.Structured.Generated.Connections.SmallSumcheck
import all Zkc.Applications.IR.Structured.Generated.Constructed.SmallSumcheckProducer
import all Zkc.Verification.Installations.Multilinear.Source.Bindings
import all Zkc.Verification.Installations.Sumcheck.Source.Checks
import all Zkc.Verification.Installations.Sumcheck.Source.Library
import all Zkc.Applications.IR.Structured.SumcheckMathBindings
import all Zkc.Verification.Installations.Sumcheck.Source.PendingBodies
import all Zkc.Verification.Installations.Sumcheck.Source.ProverLaws
import all Zkc.Verification.Installations.Sumcheck.Source.ProverProcess
import all Zkc.IR.Construction.ConnectionServiceCoverage
import all Zkc.IR.Construction.ConnectionServiceRequests
import all Zkc.IR.Construction.ConnectionServiceRoutes
import all Zkc.IR.Construction.ConnectionTargetPlacement
import all Zkc.IR.Construction.ServiceConnection
import all Zkc.IR.Construction.ServiceRequests
import all Zkc.Program.Source.LogicalFormat
import all Zkc.IR.Source.Structured.Addresses
import all Zkc.IR.Source.Structured.CatalogueEnvironment
import all Zkc.IR.Source.Structured.ContractApplication
import all Zkc.IR.Source.Structured.ContractExecution
import all Zkc.IR.Source.Structured.ContractMeaning
import all Zkc.IR.Source.Structured.ContractObligations
import all Zkc.IR.Source.Structured.CustodyAdmission
import all Zkc.IR.Source.Structured.IndexWords
import all Zkc.IR.Source.Structured.InstalledCatalogue
import all Zkc.IR.Source.Structured.LogicalContext
import all Zkc.IR.Source.Structured.LogicalInstantiation
import all Zkc.IR.Source.Structured.LogicalTranslation
import all Zkc.IR.Source.Structured.Numerical
import all Zkc.IR.Source.Structured.NumericalEvaluation
import all Zkc.IR.Source.Structured.OpaqueRegistry
import all Zkc.IR.Source.Structured.OracleAdmission
import all Zkc.IR.Source.Structured.OracleBody
import all Zkc.IR.Source.Structured.OracleOperations
import all Zkc.IR.Source.Structured.OracleProtocolAdmission
import all Zkc.IR.Source.Structured.OracleValues
import all Zkc.IR.Source.Structured.PolynomialValue
import all Zkc.IR.Source.Structured.ServiceAdmission
import all Zkc.IR.Source.Structured.ServiceExecution
import all Zkc.IR.Source.Structured.ServiceOperations
import all Zkc.IR.Source.Structured.SourceDeclarations
import all Zkc.IR.Source.Structured.SourcePlacementShape
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
