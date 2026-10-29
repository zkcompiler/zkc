import ZkcExamples.Construction.SchnorrProof
import ZkcTools.ConstructionBindings.Admission
import Tests.ConnectionRefusal

/-! Controls for complete source correspondence on the actual Schnorr validator.
The structural checks retain transcript wiring and occurrence provenance. The
default checked derivation additionally matches computations, replies and every
returned value. Refusal of that method is reported separately from a proof of
non-correspondence: symmetric equalities and dead arithmetic can be semantically
valid while needing a different proof. The admitted-source mixup controls keep
the snapshot and its typed program inseparable. -/

set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option linter.unusedTactic false
namespace Tests.SourceConnectionControls
open Zkc.Construction ZkcExamples.Construction

abbrev original := SchnorrProofData.snapshot
abbrev program := SchnorrProof.program
abbrev imported := SchnorrProof.imported
abbrev actual := SchnorrProof.participant

/-- Change one instruction, keeping every other operand and result. -/
def modify (participant : Participant) (index : Nat) (change : Instruction → Instruction) :
    Participant :=
  { participant with instructions := participant.instructions.mapIdx fun position instruction =>
      if position = index then change instruction else instruction }

theorem compiled_accepted : checkCompiled imported actual = .ok () := by decide +kernel

theorem actual_connected : ConnectionAdmission.Required program SchnorrProof.context .validator actual := by
  derive_source_connection

/-! The verifier's arithmetic. Exported positions: inputs `0` base, `1`
statement; `3` commitment, `7` challenge, `11` response; `14` is `response •
base`, `15` is `challenge • statement`, `16` is `commitment + 15` and `17` is
the decision `14 = 16`. -/

/-- The final comparison compares the base with itself. -/
def baseEqualsBase : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [0, 0] }

theorem baseEqualsBase_construction_accepted : checkExport original baseEqualsBase = .ok () := by
  decide +kernel

example : True := by
  expect_connection_refusal "baseEqualsBase" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator baseEqualsBase := by
      derive_source_connection
  trivial

/-- The response scales the statement instead of the base. -/
def responseScalesStatement : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [1, 11] }

theorem responseScalesStatement_construction_accepted :
    checkExport original responseScalesStatement = .ok () := by
  decide +kernel

example : True := by
  expect_connection_refusal "responseScalesStatement" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator responseScalesStatement := by
      derive_source_connection
  trivial

/-- The challenge, not the response, scales the base. -/
def challengeScalesBase : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [0, 7] }

theorem challengeScalesBase_construction_accepted :
    checkExport original challengeScalesBase = .ok () := by
  decide +kernel

example : True := by
  expect_connection_refusal "challengeScalesBase" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator challengeScalesBase := by
      derive_source_connection
  trivial

/-- The sum adds the scaled base, not the commitment, to the scaled statement. -/
def wrongSum : Participant :=
  modify actual 12 fun instruction => { instruction with operands := [14, 15] }

theorem wrongSum_construction_accepted : checkExport original wrongSum = .ok () := by
  decide +kernel

example : True := by
  expect_connection_refusal "wrongSum" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator wrongSum := by
      derive_source_connection
  trivial

/-- The decision compares the operands in the other order; equality is
symmetric, but the rule matches operations, not their algebra. -/
def swappedComparison : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [16, 14] }

example : True := by
  expect_connection_refusal "swappedComparison" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator swappedComparison := by
      derive_source_connection
  trivial

/-! The result selector. -/

/-- The export appends a constant and returns it as the decision: it accepts
every proof. The transcript wiring is unchanged, so the construction rule
accepts it; no original operation produces the constant. -/
def acceptAlways : Participant :=
  { actual with
    instructions := actual.instructions ++ [⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]
    returned := [18, 13] }

theorem acceptAlways_construction_accepted : checkExport original acceptAlways = .ok () := by
  decide +kernel

example : True := by
  expect_connection_refusal "acceptAlways" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator acceptAlways := by
      derive_source_connection
  trivial

/-- The export returns the sum instead of the decision. -/
theorem wrongResult_refused :
    checkCompiled imported { actual with returned := [16, 13] } =
      .error "construction-final" := by
  decide +kernel

/-- The policy selects an output the validator does not have. -/
theorem wrongAcceptance_refused :
    checkCompiled imported { actual with policy := { actual.policy with acceptance := 1 } } =
      .error "construction-acceptance" := by
  decide +kernel

/-! Roles and visibility. -/

/-- The validator's data inputs are the base and the statement; the witness is
the producer's. -/
theorem validator_data_inputs :
    (entryInterface original).map (fun (inputs, interface) =>
      dataInputs inputs interface.inputScopes actual.policy.validator) = some [0, 1] := by
  decide +kernel

/-- The export publishes the witness to the validator as a third data input. -/
def witnessPublished : Participant :=
  { actual with
    policy := { actual.policy with publicInputs := [0, 1, 2] }
    inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"),
      .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"] }

theorem witnessPublished_refused :
    checkCompiled imported witnessPublished = .error "construction-context" := by
  decide +kernel

/-! Actions, checked by the complete connection method. -/

/-- The delivery observation names the producer as its sender, so the
interactive reading no longer delivers the challenge. -/
def deliveryFromProducer : Participant :=
  modify actual 6 fun instruction => { instruction with
    operation := .observe "merlin3.bls12-381.fr64be/0" ⟨SchnorrProofData.snapshot.entry, [],
      ["message", SchnorrProofData.snapshot.entry, "label_64656c6976657279_0",
        "label_64656c6976657279_0", "role00000000", "role00000001"]⟩ }

example : True := by
  expect_connection_refusal "deliveryFromProducer" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator deliveryFromProducer := by
      derive_source_connection
  trivial

/-- The challenge is drawn at the delivery's site. -/
def challengeAtDelivery : Participant :=
  modify actual 4 fun instruction => { instruction with
    operation := .challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨SchnorrProofData.snapshot.entry,
      [], ["query", SchnorrProofData.snapshot.entry, "label_64656c6976657279_0", "input_4",
        "random.bls12-381.fr/0", "draw", "role00000001"]⟩ }

example : True := by
  expect_connection_refusal "challengeAtDelivery" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator challengeAtDelivery := by
      derive_source_connection
  trivial

/-- The response is received at the commitment's site. -/
def responseAtCommitment : Participant :=
  modify actual 7 fun instruction => { instruction with
    operation := .receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0"
      "role00000000" (.field "bls12-381.fr") }

example : True := by
  expect_connection_refusal "responseAtCommitment" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator responseAtCommitment := by
      derive_source_connection
  trivial

/-- An unused pure calculation preserves the full result and observation trace.
The checked suffix rule validates its operand frame and discards only its result. -/
def extraCalculation : Participant :=
  { actual with instructions := actual.instructions ++
      [⟨.calculate (.groupAdd "bls12-381.g1"), [0, 1], [.data (.group "bls12-381.g1")], []⟩] }

theorem extraCalculation_connected :
    ConnectionAdmission.Required program SchnorrProof.context .validator extraCalculation := by
  derive_source_connection

/-- The validator's work is dropped: the export ends after the response. -/
def truncated : Participant :=
  { actual with instructions := actual.instructions.take 10, returned := [11, 13] }

example : True := by
  expect_connection_refusal "truncated" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator truncated := by
      derive_source_connection
  trivial

/-! Source admission. -/

/-- The final top-level instruction of a body compares its latest value with
itself. -/
def selfCompareLast : Zkc.Source.Structured.Block → Zkc.Source.Structured.Block
  | .block instructions terminator =>
    .block (instructions.mapIdx fun position instruction =>
      if position + 1 = instructions.length then
        match instruction with
        | .instruction descriptor _ results regions site =>
          .instruction descriptor [0, 0] results regions site
      else instruction) terminator

/-- The original with the root protocol's final comparison replaced by a
comparison of the sum with itself. -/
def alteredSnapshot : Zkc.Source.Structured.Snapshot :=
  { original with definitions := original.definitions.map fun
      | .function function =>
        if function.name = original.entry then .function { function with body := selfCompareLast function.body }
        else .function function
      | definition => definition }

/-- The final comparison of the root protocol's body, by its operands. -/
def finalOperands (snapshot : Zkc.Source.Structured.Snapshot) : Option (List Nat) :=
  match snapshot.definitions.find? (·.name = snapshot.entry) with
  | some (.function function) =>
    match function.body with
    | .block instructions _ =>
      match instructions.getLast? with
      | some (.instruction _ operands _ _ _) => some operands
      | none => none
  | _ => none

theorem finalOperands_original : finalOperands original = some [2, 0] := by decide +kernel

theorem finalOperands_altered : finalOperands alteredSnapshot = some [0, 0] := by decide +kernel

theorem altered_differs : alteredSnapshot ≠ original := fun same => by
  have operands := congrArg finalOperands same
  rw [finalOperands_original, finalOperands_altered] at operands
  cases operands

/- Build the changed typed body using the same phased reader as production.
The raw snapshot is still checked independently, so a stale typed mutation is
rejected. Avoid defining the payload by rerunning the whole source checker. -/
namespace Altered
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Construction.SchnorrProofBodies

def compareWithSelf {inputs outputs : List Ty} :
    Region protocolDialect inputs outputs → Region protocolDialect inputs outputs
  | .ret values => .ret values
  | .stop reason => .stop reason
  | .bind body next => .bind (compareWithSelf body) (compareWithSelf next)
  | .letOp (.calculate (.groupEqual group) pure) (.cons _ (.cons right .nil)) regions next =>
      .letOp (.calculate (.groupEqual group) pure) (.cons right (.cons right .nil))
        regions (compareWithSelf next)
  | .letOp operation operands regions next =>
      .letOp operation operands regions (compareWithSelf next)

abbrev changedSignature := proofSignature
def changedBody : Region protocolDialect changedSignature.inputs changedSignature.outputs :=
  compareWithSelf proofBody

structured_views alteredSnapshot
  helpers [formula]
  protocols [changed]
end Altered

abbrev alteredProgram := Altered.program
abbrev alteredImported := Altered.imported

theorem altered_admitted : Zkc.Source.Structured.check alteredSnapshot = .ok alteredProgram :=
  Altered.kernel_admission

/-- The candidate that matches the altered program: the decision compares the
sum with itself. -/
def alteredCandidate : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [16, 16] }

/-- Against its own snapshot, the altered pair passes the composed check. -/
theorem altered_accepted : checkCompiled alteredImported alteredCandidate = .ok () := by
  decide +kernel

theorem altered_connected : ConnectionAdmission.Required alteredProgram SchnorrProof.context
    .validator alteredCandidate := by
  derive_source_connection

/-- The admission premise cannot be met: the unchanged snapshot does not admit
the altered program. -/
theorem mixed_unadmitted : Zkc.Source.Structured.check original ≠ .ok alteredProgram := fun admitted =>
  altered_differs (alteredImported.exactSubject.symm.trans
    (Zkc.Source.Structured.Imported.exactSubject (snapshot := original) ⟨alteredProgram, admitted⟩))

/-- The unchanged snapshot admits one subject, the actual program. -/
theorem subject_unique (subject : Zkc.Source.Structured.Imported original) : subject = imported := by
  obtain ⟨admittedProgram, admitted⟩ := subject
  have same : admittedProgram = SchnorrProof.program :=
    Zkc.Verification.Imported.unique ⟨admittedProgram, admitted⟩ imported
  subst same
  rfl

/-- The same altered candidate cannot use the actual source's default derivation. -/
example : True := by
  expect_connection_refusal "mixed source and candidate" because "alignment-"
    have refused : ConnectionAdmission.Required program SchnorrProof.context .validator alteredCandidate := by
      derive_source_connection
  trivial

end Tests.SourceConnectionControls
