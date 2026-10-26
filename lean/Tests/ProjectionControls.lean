import ZkcExamples.Construction.SchnorrProof

/-! Controls for the participant projection rule and the composed per-compile
check on the actual compiled Schnorr validator. The transcript-construction rule
alone checks transcript wiring, not the validator's mathematics: each
mathematical mutation below keeps that wiring and is accepted by
`checkExport`, while the composed check refuses it because the mutated
instruction implements no operation of the original validator. The last group
shows why the composed check takes an admitted original rather than a snapshot
and a program separately: an altered program with a matching candidate passes
both rules when paired with the unchanged snapshot, and only the admission
premise refuses the pair. -/

namespace Tests.ProjectionControls
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

/-! The verifier's arithmetic. Exported positions: inputs `0` base, `1`
statement; `3` commitment, `7` challenge, `11` response; `14` is `response •
base`, `15` is `challenge • statement`, `16` is `commitment + 15` and `17` is
the decision `14 = 16`. -/

/-- The final comparison compares the base with itself. -/
def baseEqualsBase : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [0, 0] }

theorem baseEqualsBase_construction_accepted : checkExport original baseEqualsBase = .ok () := by
  decide +kernel

theorem baseEqualsBase_refused :
    checkCompiled imported baseEqualsBase = .error "projection-unexplained" := by
  decide +kernel

/-- The response scales the statement instead of the base. -/
def responseScalesStatement : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [1, 11] }

theorem responseScalesStatement_construction_accepted :
    checkExport original responseScalesStatement = .ok () := by
  decide +kernel

theorem responseScalesStatement_refused :
    checkCompiled imported responseScalesStatement = .error "projection-unexplained" := by
  decide +kernel

/-- The challenge, not the response, scales the base. -/
def challengeScalesBase : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [0, 7] }

theorem challengeScalesBase_construction_accepted :
    checkExport original challengeScalesBase = .ok () := by
  decide +kernel

theorem challengeScalesBase_refused :
    checkCompiled imported challengeScalesBase = .error "projection-unexplained" := by
  decide +kernel

/-- The sum adds the scaled base, not the commitment, to the scaled statement. -/
def wrongSum : Participant :=
  modify actual 12 fun instruction => { instruction with operands := [14, 15] }

theorem wrongSum_construction_accepted : checkExport original wrongSum = .ok () := by
  decide +kernel

theorem wrongSum_refused : checkCompiled imported wrongSum = .error "projection-unexplained" := by
  decide +kernel

/-- The decision compares the operands in the other order; equality is
symmetric, but the rule matches operations, not their algebra. -/
def swappedComparison : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [16, 14] }

theorem swappedComparison_refused :
    checkCompiled imported swappedComparison = .error "projection-unexplained" := by
  decide +kernel

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

theorem acceptAlways_refused :
    checkCompiled imported acceptAlways = .error "projection-unexplained" := by
  decide +kernel

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

/-! Actions, checked by the projection rule alone. -/

/-- The delivery observation names the producer as its sender, so the
interactive reading no longer delivers the challenge. -/
def deliveryFromProducer : Participant :=
  modify actual 6 fun instruction => { instruction with
    operation := .observe "merlin3.bls12-381.fr64be/0" ⟨SchnorrProofData.snapshot.entry, [],
      ["message", SchnorrProofData.snapshot.entry, "label_64656c6976657279_0",
        "label_64656c6976657279_0", "role00000000", "role00000001"]⟩ }

theorem deliveryFromProducer_projection_refused :
    project program SchnorrProof.context deliveryFromProducer = .error "projection-delivery" := by
  decide +kernel

/-- The challenge is drawn at the delivery's site. -/
def challengeAtDelivery : Participant :=
  modify actual 4 fun instruction => { instruction with
    operation := .challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨SchnorrProofData.snapshot.entry,
      [], ["query", SchnorrProofData.snapshot.entry, "label_64656c6976657279_0", "input_4",
        "random.bls12-381.fr/0", "draw", "role00000001"]⟩ }

theorem challengeAtDelivery_projection_refused :
    project program SchnorrProof.context challengeAtDelivery = .error "projection-challenge" := by
  decide +kernel

/-- The response is received at the commitment's site. -/
def responseAtCommitment : Participant :=
  modify actual 7 fun instruction => { instruction with
    operation := .receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0"
      "role00000000" (.field "bls12-381.fr") }

theorem responseAtCommitment_projection_refused :
    project program SchnorrProof.context responseAtCommitment = .error "projection-receive" := by
  decide +kernel

/-- An extra calculation that no original operation accounts for. -/
def extraCalculation : Participant :=
  { actual with instructions := actual.instructions ++
      [⟨.calculate (.groupAdd "bls12-381.g1"), [0, 1], [.data (.group "bls12-381.g1")], []⟩] }

theorem extraCalculation_projection_refused :
    project program SchnorrProof.context extraCalculation = .error "projection-unexplained" := by
  decide +kernel

/-- The validator's work is dropped: the export ends after the response. -/
def truncated : Participant :=
  { actual with instructions := actual.instructions.take 10, returned := [11, 13] }

theorem truncated_projection_refused :
    project program SchnorrProof.context truncated = .error "projection-outputs" := by
  decide +kernel

/-! Source admission. -/

/-- The composition without the admission link: the construction rule against
one snapshot and the projection rule against any program. -/
def unlinkedCheck (snapshot : Zkc.Source.Structured.Snapshot) (program : Zkc.Source.Structured.Program)
    (participant : Participant) : Except String Unit :=
  match checkExport snapshot participant, exportContext snapshot participant with
  | .ok (), some context => project program context participant
  | .error error, _ => .error error
  | .ok (), none => .error "construction-context"

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

set_option smartUnfolding true in
/-- The altered snapshot admits. -/
theorem altered_admissible : (Zkc.Source.Structured.check alteredSnapshot).toOption.isSome = true := by
  decide +kernel

/-- The program the altered snapshot admits. -/
def alteredProgram : Zkc.Source.Structured.Program :=
  (Zkc.Source.Structured.check alteredSnapshot).toOption.get altered_admissible

theorem altered_admitted : Zkc.Source.Structured.check alteredSnapshot = .ok alteredProgram := by
  have found : (Zkc.Source.Structured.check alteredSnapshot).toOption = some alteredProgram :=
    (Option.some_get altered_admissible).symm
  revert found
  cases Zkc.Source.Structured.check alteredSnapshot <;> simp [Except.toOption]

def alteredImported : Zkc.Source.Structured.Imported alteredSnapshot := ⟨alteredProgram, altered_admitted⟩

/-- The candidate that matches the altered program: the decision compares the
sum with itself. -/
def alteredCandidate : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [16, 16] }

/-- Paired with the unchanged snapshot, the altered program and its candidate
pass both rules: the construction rule against the original snapshot and the
projection rule against the altered program. -/
theorem unlinked_accepts_mixed : unlinkedCheck original alteredProgram alteredCandidate = .ok () := by
  decide +kernel

/-- Against its own snapshot, the altered pair passes the composed check. -/
theorem altered_accepted : checkCompiled alteredImported alteredCandidate = .ok () := by
  decide +kernel

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

/-- So every admitted subject of the unchanged snapshot refuses the altered
candidate. -/
theorem mixed_refused (subject : Zkc.Source.Structured.Imported original) :
    checkCompiled subject alteredCandidate = .error "projection-unexplained" := by
  rw [subject_unique subject]
  decide +kernel

end Tests.ProjectionControls
