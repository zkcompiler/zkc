import Zkc.Executable.DomainNormalizationSoundness
import Zkc.Executable.Reading
import Zkc.Executable.Installed
import ZkcExamples.Executable.SchnorrProofProgramData
import ZkcExamples.Executable.SumcheckProofProgramData
import ZkcExamples.Construction.SchnorrProofParticipant
import ZkcExamples.Construction.SumcheckProofParticipant
import ZkcExamples.Executable.DeferredRoundsDomainNormalization

/-! Admission controls use actual generated native and participant artifacts.
They do not import the retired executable proof consumers. -/
namespace Tests.CanonicalNormalizationExamples
open Zkc.Construction Zkc.Executable

/-- Read the actual artifact and check canonical normalization against its
participant, including the exact ordered return selection and output schema. -/
def certified (participant : Participant) (validator : Validator) : Bool :=
  match Validator.read installed (Instruction.helperList participant.instructions) validator with
  | .error _ => false
  | .ok reading =>
      (CanonicalNormalization.check participant.inputs participant.outputs
        participant.instructions participant.returned
        (Code.instructionList reading.code) reading.returned).toOption.isSome

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem schnorr_admitted :
    certified ZkcExamples.Construction.SchnorrProofParticipant.participant
      ZkcExamples.Executable.SchnorrProofProgramData.validator = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sumcheck_admitted :
    certified ZkcExamples.Construction.SumcheckProofParticipant.participant
      ZkcExamples.Executable.SumcheckProofProgramData.validator = true := by
  decide +kernel

/-- DeferredRounds exercises the genuinely distinct native schedule. -/
theorem deferred_admitted :
    (CanonicalNormalization.check
      ZkcExamples.Construction.DeferredRounds.participant.inputs
      ZkcExamples.Construction.DeferredRounds.participant.outputs
      ZkcExamples.Construction.DeferredRounds.participant.instructions
      ZkcExamples.Construction.DeferredRounds.participant.returned
      ZkcExamples.Executable.DeferredRounds.readingInstructions [23, 17]).toOption.isSome = true :=
  ZkcExamples.Executable.DeferredRounds.normalization_checked

end Tests.CanonicalNormalizationExamples
