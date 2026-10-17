import ZkcExamples.Construction.SchnorrProof
import ZkcExamples.Structured.SchnorrInteractiveData

/-! Controls for the transcript-construction rule on the actual compiled Schnorr
validator. The accepted export satisfies the premises of `check_sound`; each
mutation below changes one obligation of the same export and must be rejected.
`check_sound` itself uses only the instruction walk (`checkFrom`); the final
clauses of `check` and the comparisons with the original in `checkExport` are
deployment checks, exercised here as well. -/

namespace Tests.ConstructionControls
open Zkc.Construction ZkcExamples.Construction

abbrev original := SchnorrProofData.snapshot
abbrev actual := SchnorrProof.participant

/-- Change one instruction, keeping every other operand and result. -/
def modify (participant : Participant) (index : Nat) (change : Instruction → Instruction) :
    Participant :=
  { participant with instructions := participant.instructions.mapIdx fun position instruction =>
      if position = index then change instruction else instruction }

/-- An exported instruction by position. -/
def exported (index : Nat) : Instruction := actual.instructions.getD index ⟨.unsupported "", [], []⟩

/-- Exported positions: inputs `0` base, `1` statement, `2` host transcript;
`3` commitment, `5` its observation, `7` challenge, `8` state after the
challenge, `10` delivery observation, `11` response, `13` final state. -/
theorem layout :
    actual.instructions.map (·.operands) =
      [[], [], [2, 3, 4], [], [5, 6], [], [8, 7, 9], [], [], [10, 11, 12], [0, 11], [1, 7],
        [3, 15], [14, 16]] ∧ actual.returned = [17, 13] := by
  decide +kernel

theorem accepted : checkExport original actual = true := SchnorrProof.accepted

/-- The mutation helper alone preserves acceptance. -/
theorem unchanged_accepted : checkExport original (modify actual 2 id) = true := by
  decide +kernel

/-! Weak Fiat–Shamir: the commitment or the statement is missing from the
challenge's hash input. -/

/-- The first observation absorbs the base instead of the received commitment. -/
def commitmentOmitted : Participant :=
  modify actual 2 fun instruction => { instruction with operands := [2, 0, 4] }

theorem commitmentOmitted_rejected : checkExport original commitmentOmitted = false := by
  decide +kernel

/-- The policy no longer publishes the statement, so the host binding omits it. -/
def statementOmitted : Participant :=
  { actual with policy := { actual.policy with publicInputs := [0] } }

theorem statementOmitted_rejected : checkExport original statementOmitted = false := by
  decide +kernel

/-! A challenge derived before the commitment is absorbed. -/

/-- The challenge reads the host transcript, not the state after observing the
commitment. -/
def challengeBeforeCommitment : Participant :=
  modify actual 4 fun instruction => { instruction with operands := [2, 6] }

theorem challengeBeforeCommitment_rejected :
    checkExport original challengeBeforeCommitment = false := by
  decide +kernel

/-- The commitment observation is moved after the challenge. -/
def observationAfterChallenge : Participant :=
  { actual with instructions :=
      [exported 0, exported 1,
        { exported 4 with operands := [2, 4] },
        exported 3,
        { exported 2 with operands := [6, 3, 7] }] ++ actual.instructions.drop 5 }

theorem observationAfterChallenge_rejected :
    checkExport original observationAfterChallenge = false := by
  decide +kernel

/-! Wrong domain separation. -/

def challengeAt (origin : Origin) : Participant :=
  modify actual 4 fun instruction => { instruction with
    operation := .challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" origin }

/-- The challenge carries the delivery's site instead of the query's. -/
theorem wrongChallengeSite_rejected :
    checkExport original (challengeAt (SchnorrProof.context.query
      SchnorrProof.wiring.deliverySite)) = false := by
  decide +kernel

/-- The challenge is labelled as a UniformIndex request. -/
theorem wrongChallengeMethod_rejected :
    checkExport original (challengeAt ⟨SchnorrProofData.snapshot.entry,
      ["query", SchnorrProofData.snapshot.entry, "label_6368616c6c656e6765", "input_4",
        "random.bls12-381.fr/0", "index", "role00000001"]⟩) = false := by
  decide +kernel

/-- The challenge names another entry. -/
theorem wrongChallengeEntry_rejected :
    checkExport original (challengeAt ⟨"other-entry",
      ["query", "other-entry", "label_6368616c6c656e6765", "input_4",
        "random.bls12-381.fr/0", "draw", "role00000001"]⟩) = false := by
  decide +kernel

/-- The commitment observation swaps sender and receiver. -/
theorem wrongMessageDirection_rejected :
    checkExport original (modify actual 2 fun instruction => { instruction with
      operation := .observe "merlin3.bls12-381.fr64be/0"
        (SchnorrProof.context.message SchnorrProof.wiring.commitmentSite 1 0) }) = false := by
  decide +kernel

/-- An observation uses another transcript suite. -/
theorem wrongSuite_rejected :
    checkExport original (modify actual 2 fun instruction => { instruction with
      operation := .observe "merlin3.ristretto255.scalar64le/0"
        (SchnorrProof.context.message SchnorrProof.wiring.commitmentSite 0 1) }) = false := by
  decide +kernel

/-! Other transcript obligations. -/

/-- The delivery observation absorbs the commitment instead of the challenge. -/
theorem deliveryNotObserved_rejected :
    checkExport original (modify actual 6 fun instruction => { instruction with
      operands := [8, 3, 9] }) = false := by
  decide +kernel

/-- An earlier transcript state is returned as the final state. -/
theorem staleFinalState_rejected :
    checkExport original { actual with returned := [17, 10] } = false := by
  decide +kernel

/-- An unsupported operation in place of the response observation. -/
theorem unsupported_rejected :
    checkExport original (modify actual 9 fun instruction => { instruction with
      operation := .unsupported "crypto.exec.other" }) = false := by
  decide +kernel

/-- A policy selecting no draw cannot account for the constructed challenge. -/
theorem noChallenge_rejected :
    checkExport original { actual with policy := { actual.policy with draws := [] } } = false := by
  decide +kernel

/-! Further clauses of the rule, one mutation each. -/

/-- The policy selects the same draw twice. -/
theorem duplicateDraw_rejected :
    checkExport original { actual with policy := { actual.policy with
      draws := actual.policy.draws ++ actual.policy.draws } } = false := by
  decide +kernel

/-- The policy selects a second draw that the export never challenges. -/
theorem missingChallenge_rejected :
    checkExport original { actual with policy := { actual.policy with
      draws := actual.policy.draws ++ [("label_6368616c6c656e6765", "label_726573706f6e7365_0")] } } =
      false := by
  decide +kernel

/-- A second challenge with no selected draw left. -/
theorem extraChallenge_rejected :
    checkExport original (modify actual 10 fun _ =>
      ⟨exported 4 |>.operation, [13, 12], [.data (.field "bls12-381.fr"),
        .transcript "merlin3.bls12-381.fr64be/0"]⟩) = false := by
  decide +kernel

/-- An observation with nothing pending absorbs extra data. -/
theorem extraObservation_rejected :
    checkExport original (modify actual 10 fun _ =>
      ⟨exported 9 |>.operation, [13, 11, 12], [.transcript "merlin3.bls12-381.fr64be/0"]⟩) =
      false := by
  decide +kernel

/-- A calculation runs before the received commitment is observed. -/
theorem calculationBeforeObservation_rejected :
    checkExport original (modify actual 1 fun _ =>
      ⟨.calculate (.groupAdd "bls12-381.g1"), [0, 0], [.data (.group "bls12-381.g1")]⟩) = false := by
  decide +kernel

/-- A calculation reads the host transcript. -/
theorem calculationReadsTranscript_rejected :
    checkExport original (modify actual 10 fun instruction =>
      { instruction with operands := [2, 11] }) = false := by
  decide +kernel

/-- The commitment is received from the validator itself. -/
theorem wrongPeer_rejected :
    checkExport original (modify actual 0 fun _ =>
      ⟨.receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000001"
        (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")]⟩) = false := by
  decide +kernel

/-- The commitment's schema differs from its site. -/
theorem wrongSchema_rejected :
    checkExport original (modify actual 0 fun _ =>
      ⟨.receive "label_636f6d6d69746d656e74_0" "label_726573706f6e7365_0" "role00000000"
        (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")]⟩) = false := by
  decide +kernel

/-- The challenge produces another field than the replaced service's. -/
theorem wrongChallengeField_rejected :
    checkExport original (modify actual 4 fun instruction =>
      { instruction with
        operation := .challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fq"
          (SchnorrProof.context.query SchnorrProof.wiring.challengeSite),
        results := [.data (.field "bls12-381.fq"), .transcript "merlin3.bls12-381.fr64be/0"] }) =
      false := by
  decide +kernel

/-- The last returned value is the decision, not the final transcript. -/
theorem dataReturnedLast_rejected :
    checkExport original { actual with returned := [13, 17] } = false := by
  decide +kernel

/-- The policy replaces the prover's nonce service instead of the validator's. -/
theorem proverService_rejected :
    checkExport original { actual with policy := { actual.policy with services := [3] } } =
      false := by
  decide +kernel

/-- The exported data inputs differ from the published validator inputs. -/
theorem wrongInputSort_rejected :
    checkExport original { actual with inputs := [.data (.field "bls12-381.fr"),
      .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"] } = false := by
  decide +kernel

/-! Identity of the pair. -/

/-- The export names another source digest than the original. -/
theorem otherSource_rejected :
    checkExport original { actual with source := ZkcExamples.Structured.SchnorrInteractiveData.snapshot.source } =
      false := by
  decide +kernel

/-- The Interactive Entry's export, with the same protocol but another source
digest, does not certify this compiled validator. -/
theorem otherOriginal_rejected :
    checkExport ZkcExamples.Structured.SchnorrInteractiveData.snapshot actual = false := by
  decide +kernel

/-- The policy selects raw-byte framing. -/
theorem rawFraming_rejected :
    checkExport original { actual with policy := { actual.policy with format := "raw.bytes/0" } } =
      false := by
  decide +kernel

/-- The policy selects an acceptance output the validator does not have. -/
theorem wrongAcceptance_rejected :
    checkExport original { actual with policy := { actual.policy with acceptance := 1 } } =
      false := by
  decide +kernel

/-- The export returns an extra data output. -/
theorem extraOutput_rejected :
    checkExport original { actual with outputs := [.data .boolean, .data .boolean,
      .transcript "merlin3.bls12-381.fr64be/0"] } = false := by
  decide +kernel

end Tests.ConstructionControls
