import ZkcExamples.Construction.SchnorrProof

/-! Controls for the participant projection rule and the composed per-compile
check on the actual compiled Schnorr validator. The transcript-construction rule
alone checks transcript wiring, not the validator's mathematics: each
mathematical mutation below keeps that wiring and is accepted by
`checkExport`, while the composed check refuses it because the mutated
instruction implements no operation of the original validator. -/

namespace Tests.ProjectionControls
open Zkc.Construction ZkcExamples.Construction

abbrev original := SchnorrProofData.snapshot
abbrev program := SchnorrProof.program
abbrev actual := SchnorrProof.participant

/-- Change one instruction, keeping every other operand and result. -/
def modify (participant : Participant) (index : Nat) (change : Instruction → Instruction) :
    Participant :=
  { participant with instructions := participant.instructions.mapIdx fun position instruction =>
      if position = index then change instruction else instruction }

theorem compiled_accepted : checkCompiled original program actual = .ok () := SchnorrProof.compiled

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
    checkCompiled original program baseEqualsBase = .error "projection-unexplained" := by
  decide +kernel

/-- The response scales the statement instead of the base. -/
def responseScalesStatement : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [1, 11] }

theorem responseScalesStatement_construction_accepted :
    checkExport original responseScalesStatement = .ok () := by
  decide +kernel

theorem responseScalesStatement_refused :
    checkCompiled original program responseScalesStatement = .error "projection-unexplained" := by
  decide +kernel

/-- The challenge, not the response, scales the base. -/
def challengeScalesBase : Participant :=
  modify actual 10 fun instruction => { instruction with operands := [0, 7] }

theorem challengeScalesBase_construction_accepted :
    checkExport original challengeScalesBase = .ok () := by
  decide +kernel

theorem challengeScalesBase_refused :
    checkCompiled original program challengeScalesBase = .error "projection-unexplained" := by
  decide +kernel

/-- The sum adds the scaled base, not the commitment, to the scaled statement. -/
def wrongSum : Participant :=
  modify actual 12 fun instruction => { instruction with operands := [14, 15] }

theorem wrongSum_construction_accepted : checkExport original wrongSum = .ok () := by
  decide +kernel

theorem wrongSum_refused : checkCompiled original program wrongSum = .error "projection-unexplained" := by
  decide +kernel

/-- The decision compares the operands in the other order; equality is
symmetric, but the rule matches operations, not their algebra. -/
def swappedComparison : Participant :=
  modify actual 13 fun instruction => { instruction with operands := [16, 14] }

theorem swappedComparison_refused :
    checkCompiled original program swappedComparison = .error "projection-unexplained" := by
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
    checkCompiled original program acceptAlways = .error "projection-unexplained" := by
  decide +kernel

/-- The export returns the sum instead of the decision. -/
theorem wrongResult_refused :
    checkCompiled original program { actual with returned := [16, 13] } =
      .error "construction-final" := by
  decide +kernel

/-- The policy selects an output the validator does not have. -/
theorem wrongAcceptance_refused :
    checkCompiled original program { actual with policy := { actual.policy with acceptance := 1 } } =
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
    checkCompiled original program witnessPublished = .error "construction-context" := by
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

end Tests.ProjectionControls
