module

-- Maintained by audit_imports.py; private bodies are required.
import all ProtocolProof
import all ProtocolProof.Claims.Assembly
import all ProtocolProof.Claims.Closure
import all ProtocolProof.Claims.Completeness
import all ProtocolProof.Claims.Diagnostics
import all ProtocolProof.Claims.Extraction
import all ProtocolProof.Claims.Problem
import all ProtocolProof.Claims.Quantitative
import all ProtocolProof.Claims.Receipt
import all ProtocolProof.Claims.Recovery
import all ProtocolProof.Claims.Request
import all ProtocolProof.Claims.Simulation
import all ProtocolProof.Claims.Soundness
import all ProtocolProof.Claims.Transfer
import all ProtocolProof.Claims.View
import all ProtocolProof.Components.Adequacy
import all ProtocolProof.Components.Contract
import all ProtocolProof.Components.Installation
import all ProtocolProof.Components.Interpretation
import all ProtocolProof.Components.Representation
import all ProtocolProof.Components.ServiceInstallation
import all ProtocolProof.Internal.Closure
import all ProtocolProof.Internal.Contract
import all ProtocolProof.Internal.Installation
import all ProtocolProof.Internal.Interpretation
import all ProtocolProof.Internal.Process
import all ProtocolProof.Internal.Quantitative
import all ProtocolProof.Internal.Representation
import all ProtocolProof.Internal.Resource
import all ProtocolProof.Internal.System
import all ProtocolProof.Semantics.Access
import all ProtocolProof.Semantics.EventLog
import all ProtocolProof.Semantics.Execution
import all ProtocolProof.Semantics.Experiment
import all ProtocolProof.Semantics.Probability
import all ProtocolProof.Semantics.Quantitative
import all ProtocolProof.Semantics.System
import all ProtocolProofExamples
import all ProtocolProofExamples.AdaptiveChecks
import all ProtocolProofExamples.BoundaryControls
import all ProtocolProofExamples.ClaimBoundaries
import all ProtocolProofExamples.ContractControls
import all ProtocolProofExamples.ExecutionControls
import all ProtocolProofExamples.InterpretationModels
import all ProtocolProofExamples.OracleProximity
import all ProtocolProofExamples.PropertyProfiles
import all ProtocolProofExamples.ServiceDecoding
import all ProtocolProofExamples.SharedState
import all ProtocolProofExamples.TransferControls
import Lean.Util.CollectAxioms


/-!
Audit every declaration owned by this package, including generated and private declarations.
Dependencies are traversed by Lean's axiom collector; only the standard logical axioms are
allowed. The package's ordinary build separately kernel-checks each theorem.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let owned := fun moduleName : Name ↦
    (`ProtocolProof).isPrefixOf moduleName || (`ProtocolProofExamples).isPrefixOf moduleName
  for imported in environment.header.modules do
    if owned imported.module && !imported.importAll then
      throwError "Proof audit requires private module data: {imported.module}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let owner := environment.header.moduleNames[index.toNat]!
    unless owned owner do continue
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Nonstandard axiom {axiomName} in {name} (module {owner})"
    checked := checked + 1
  if checked == 0 then
    throwError "No proof declarations were audited"
  logInfo m!"Axiom audit passed: {checked} package declarations; only propext, Classical.choice, Quot.sound."
