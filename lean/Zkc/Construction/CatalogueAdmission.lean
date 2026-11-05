module

public import Zkc.Construction.Participant
public import Zkc.Source.Structured.Admission

@[expose] public section

/-! Catalogue admission of an exported constructed participant.

The export carries the native rows of every identity the participant names,
closed under associated members, and the rows of the random services its ports
name. The bridge renders them as the `catalogue` declaration beside the
participant. The renderer projects binding members and capability facts through
those rows; it certifies nothing. `Participant.checkCatalogue` is the
authority: the rows must be consistent (`Catalogue.check`), equal the
environment's rows (`Catalogue.agrees`), give every stored sort an admitted
instance, list the policy suite and every port's service, and supply each
association an operation names: a challenge's field is its suite's
`ChallengeField`, an embedding's base is its extension's `BaseField`, a scaling
field is its group's `Scalar`, and a local request is a method of its service at
the field the service samples. A row the environment omits refuses with
`structured-catalogue-unknown`.

Admission of the rows is separate from the construction rule and from the laws
of any field, group or transcript the rows name. -/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source

mutual
/-- Each operation of an instruction with its result sorts, loop bodies included. -/
def Instruction.storedOf : Instruction → List (Operation × List ValueSort)
  | ⟨operation, _, results, body⟩ => (operation, results) :: Instruction.storedList body

/-- Each operation of an instruction list with its result sorts, in order,
loop bodies included. -/
def Instruction.storedList : List Instruction → List (Operation × List ValueSort)
  | [] => []
  | instruction :: rest => Instruction.storedOf instruction ++ Instruction.storedList rest
end

/-- A transcript suite row with the capability an operation requires. -/
def requireSuite (catalogue : Structured.Catalogue) (suite capability : String) :
    Except String Structured.Nominal := do
  let row ← catalogue.expect suite .transcript
  if !row.holds capability then throw "structured-domain-capability"
  return row

/-- An admitted value sort: data through the structured instance check, a
transcript capability through its suite's row. -/
def checkValueSort (exported environment : Structured.Catalogue) : ValueSort → Except String Unit
  | .data ty => exported.checkType environment ty
  | .transcript suite => discard <| requireSuite exported suite "Transcript"
  | .indices => pure ()

/-- The catalogue facts an operation names. -/
def checkOperationCatalogue (catalogue : Structured.Catalogue) : Operation → Except String Unit
  | .observe suite _ => discard <| requireSuite catalogue suite "Transcript"
  | .challenge suite field _ => do
      let row ← requireSuite catalogue suite "FieldTranscript"
      if row.member "ChallengeField" != some field then throw "structured-domain-member"
  | .indexChallenge suite _ _ => discard <| requireSuite catalogue suite "IndexTranscript"
  | .blockChallenge suite _ _ _ => discard <| requireSuite catalogue suite "IndexBlockTranscript"
  | .localService port request _ _ => do
      let service ← catalogue.findService port.contract
      if !request.valid || !(request.operation port.contract).isSome ||
          !service.methods.contains request.method then throw "structured-service-contract"
      match request.method, request.sort with
      | "draw", .field field =>
          if field != service.sampled then throw "structured-service-contract"
      | "index", .index =>
          let row ← catalogue.expect service.sampled .field
          if !row.holds "IndexRandomness" then throw "structured-domain-capability"
      | "indices", .indices =>
          let row ← catalogue.expect service.sampled .field
          if !row.holds "IndexBlockRandomness" then throw "structured-domain-capability"
      | _, _ => throw "structured-service-contract"
  | .calculate (.fieldEmbed extension base) => catalogue.requireEmbedding extension base
  | .calculate (.groupScale group field) => catalogue.requireScale group field
  | _ => pure ()

/-- Admission of the catalogue rows exported with a participant against the
environment's rows. -/
def Participant.checkCatalogue (participant : Participant)
    (catalogue environment : Structured.Catalogue) : Except String Unit := do
  catalogue.check
  catalogue.agrees environment
  let stored := Instruction.storedList participant.instructions
  (participant.inputs ++ participant.outputs ++ stored.flatMap (·.2)).forM
    (checkValueSort catalogue environment)
  if participant.policy.suite != "" then
    discard <| requireSuite catalogue participant.policy.suite "Transcript"
  participant.servicePorts.forM fun port => discard <| catalogue.findService port.contract
  stored.forM fun (operation, _) => checkOperationCatalogue catalogue operation

end Zkc.Construction
