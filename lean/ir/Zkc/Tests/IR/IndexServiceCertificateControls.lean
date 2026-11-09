module

public import Zkc.Tests.IR.IndexServiceCertificates
public import Zkc.Tests.IR.IndexServicesPrivate

@[expose] public section

/-! Accepted layout controls and refused mutations for actual tiny roots. -/
-- Whole-root connection proposals retain large kernel terms. Check the roots
-- in source order so independent proofs do not compete for memory.
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Tests.IndexServiceCertificateControls
open Zkc.Source Zkc.Source.Structured Zkc.Construction Tests.IndexServices

/-- Add a real total instruction before the scalar layout and relocate every
existing data reference. The original transcript input stays at location zero. -/
def shiftedScalar : Participant :=
  let shift := fun reference => if reference = 0 then 0 else reference + 1
  { Scalar.Validator.participant with
    instructions := ⟨.calculate (.indexConstant 99), [], [.data .index], []⟩ ::
      Scalar.Validator.participant.instructions.map fun instruction =>
        { instruction with operands := instruction.operands.map shift }
    returned := Scalar.Validator.participant.returned.map shift }

theorem shifted_scalar_connected :
    ConnectionAdmission.Required Scalar.program Scalar.context .validator shiftedScalar := by
  derive_source_connection

/-- Extend the one actual loop region, preserving its ABI and return positions.
An unexpected region count cannot silently leave the positive control unchanged. -/
def extendedRepeat : Participant :=
  { Repeated.Validator.participant with
    instructions := Repeated.Validator.participant.instructions.map fun instruction =>
      match instruction.operation, instruction.regions with
      | .loop .., [region] => { instruction with regions := [{region with instructions :=
          region.instructions ++ [⟨.calculate (.indexConstant 99), [], [.data .index], []⟩]}] }
      | _, _ => instruction }

example : extendedRepeat.instructions ≠ Repeated.Validator.participant.instructions := by decide +kernel

theorem extended_repeat_connected :
    ConnectionAdmission.Required Repeated.program Repeated.context .validator extendedRepeat := by
  derive_source_connection

def wrongRequest : Participant :=
  { Scalar.Validator.participant with
    instructions := Scalar.Validator.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .indexChallenge suite _ template =>
        { instruction with operation := .indexChallenge suite 16 template }
      | _ => instruction }

def wrongReference : Participant :=
  { Scalar.Validator.participant with
    instructions := Scalar.Validator.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .indexChallenge .. => { instruction with operands := [0, 0, 3] }
      | _ => instruction }

def wrongArity : Participant :=
  { Scalar.Validator.participant with
    instructions := Scalar.Validator.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .indexChallenge .. => { instruction with operands := instruction.operands.take 2 }
      | _ => instruction }

def wrongCount : Participant :=
  { Block.Validator.participant with
    instructions := Block.Validator.participant.instructions.map fun instruction =>
      match instruction.operation with
      | .blockChallenge suite bound _ template =>
        { instruction with operation := .blockChallenge suite bound 2 template }
      | _ => instruction }

def wrongAncestry : Participant :=
  { Repeated.Validator.participant with
    instructions := Repeated.Validator.participant.instructions.map fun instruction =>
      { instruction with regions := instruction.regions.map fun region =>
          { region with instructions := region.instructions.map fun step =>
              match step.operation with
              | .indexChallenge suite bound template =>
                { step with operation := .indexChallenge suite bound { template with steps := [] } }
              | _ => step } } }

example : wrongAncestry.instructions ≠ Repeated.Validator.participant.instructions := by decide +kernel


namespace Outcomes
open Tests.IndexServices.Execution

def localPair (model : DomainModel) := Domain.executePair model Local.program Local.context
  Local.Producer.participant Local.Validator.participant [.transcript suite []] [.transcript suite []]
  (fixedOracle model.toCarriers) 0 (Private.replies model.toCarriers)

theorem local_accepts (model : DomainModel) :
    ((localPair model).validator.map fun execution => returnedAcceptance execution.outcome) =
      some true := by kernel_rfl

theorem local_private_public_effects (model : DomainModel) :
    ((localPair model).validator.map fun execution => execution.state.oracle) = some 302 := by kernel_rfl

def repeatedPair (model : DomainModel) := Domain.executePair model Repeated.program Repeated.context
  Repeated.Producer.participant Repeated.Validator.participant [.transcript suite []] [.transcript suite []]
  (fixedOracle model.toCarriers) 0

theorem repeated_accepts (model : DomainModel) :
    ((repeatedPair model).validator.map fun execution => returnedAcceptance execution.outcome) =
      some true := by kernel_rfl

theorem repeated_queries_remain_separate (model : DomainModel) :
    ((repeatedPair model).validator.map fun execution => execution.state.oracle) = some 6 := by kernel_rfl

/-- A stop on the second public query keeps the first query/message pair and
then the attempted second query, with its exact occurrence coordinate. -/
def stopSecond (carriers : Carriers) : Domain.Oracle Id carriers Nat :=
  fun kind event state => match event with
  | .challenge origin => if state = 1 then (.stopped .exhausted, 42)
      else fixedOracle carriers kind (.challenge origin) state
  | .message .. | .publicBinding .. => (.returned (), state)

def failedRepeat (model : DomainModel) := Domain.produce model Repeated.program Repeated.context
  Repeated.Producer.participant [.transcript suite []] (stopSecond model.toCarriers) 0

theorem stopped_reason (model : DomainModel) :
    (failedRepeat model).outcome = .stopped .exhausted := by kernel_rfl
theorem stopped_state (model : DomainModel) : (failedRepeat model).state.oracle = 42 := by kernel_rfl
theorem stopped_prefix (model : DomainModel) :
    (failedRepeat model).events = [
      .challenge (Domain.atCoordinates (Repeated.context.query "label_706f736974696f6e" (.sampleIndex 8)) [0]),
      .message (Domain.atCoordinates (Repeated.context.message "label_64656c6976657279_0" 1 0) [0]) (.index 3),
      .challenge (Domain.atCoordinates (Repeated.context.query "label_706f736974696f6e" (.sampleIndex 8)) [1])
    ] := by kernel_rfl
end Outcomes

#print axioms Scalar.validator_connected
#print axioms Scalar.producer_connected
#print axioms Block.validator_connected
#print axioms Block.producer_connected
#print axioms Local.validator_connected
#print axioms Local.producer_connected
#print axioms Repeated.validator_connected
#print axioms Repeated.producer_connected
#print axioms shifted_scalar_connected
#print axioms extended_repeat_connected
end Tests.IndexServiceCertificateControls
