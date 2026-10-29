import Zkc.Construction.ConnectionOrigins
import ZkcExamples.Construction.SchnorrArtifact
import Zkc.Construction.DomainExecution
import ZkcExamples.Construction.SumcheckProofParticipant
import ZkcExamples.Structured.SumcheckSourceData

set_option autoImplicit false
set_option smartUnfolding true
set_option maxRecDepth 10000

namespace Tests.SourceOccurrences
open Zkc.Construction
open Zkc.Construction.SourceOccurrences

private abbrev snapshot := ZkcExamples.Structured.SumcheckSourceData.snapshot
private abbrev exported := ZkcExamples.Construction.SumcheckProofParticipant.participant
private def context : Context :=
  Context.fiatShamir (exported.policy.entry) (["role00000000", "role00000001"]) 0 1 3 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) (exported.policy.suite) (exported.policy.draws)

private def loopBody : List Instruction :=
  match exported.instructions[2]? with
  | some instruction => instruction.body
  | none => []

private def messageTemplate : Template :=
  match loopBody[3]? with
  | some instruction =>
      match instruction.operation with
      | .observe _ template => template
      | _ => ⟨"invalid-fixture", [], []⟩
  | _ => ⟨"invalid-fixture", [], []⟩

private def queryTemplate : Template :=
  match loopBody[13]? with
  | some instruction =>
      match instruction.operation with
      | .challenge _ _ template => template
      | _ => ⟨"invalid-fixture", [], []⟩
  | _ => ⟨"invalid-fixture", [], []⟩

-- The unchanged real export has a root Entry, a different local definition,
-- and local input_6 transported from root input_3 through an apply and repeat.
example : valid snapshot context messageTemplate = true := by decide +kernel
example : valid snapshot context queryTemplate = true := by decide +kernel
example : check snapshot context exported = .ok () := by decide +kernel
example : messageTemplate.event[1]? ≠ some context.entry := by decide +kernel
example : queryTemplate.event[3]? = some "input_6" := by decide +kernel
example : (Domain.templateOrigin context messageTemplate [0]).isSome = true := by decide +kernel
example : (Domain.queryOrigin context context.suite "bls12-381.fr" queryTemplate [0]).isSome = true := by
  decide +kernel
example : Domain.queryOrigin context context.suite "bls12-381.fr" queryTemplate [] = none := by
  decide +kernel

private def messageOrigin : Origin :=
  context.message (messageTemplate.qualify (messageTemplate.event[2]?.getD "")) 0 1

private theorem static_message : OccurrenceResolution.resolveStatic snapshot context messageOrigin
    (repeatSites messageTemplate) [messageTemplate] = some messageTemplate := by decide +kernel

-- The actual apply/repeat export has one finite certificate for every reached
-- index, including indices unequal to zero. No runtime count is unfolded.
example (index : Nat) :
    OccurrenceResolution.resolve snapshot context messageOrigin
      [⟨(repeatSites messageTemplate).headD "", index⟩] [messageTemplate] =
      some (Domain.atCoordinates messageOrigin [index]) :=
  OccurrenceResolution.resolve_of_static static_message _ (by rfl)

example : OccurrenceResolution.resolveStatic snapshot context messageOrigin
    (repeatSites messageTemplate) [] = none := rfl

example : OccurrenceResolution.resolveStatic snapshot context messageOrigin
    (repeatSites messageTemplate) [messageTemplate, messageTemplate] = none := by decide +kernel

example : OccurrenceResolution.resolveStatic snapshot context messageOrigin
    ["different-loop"] [messageTemplate] = none := by decide +kernel

-- A normalized root port must not be accepted as retained local source data.
example : valid snapshot context { queryTemplate with
    event := queryTemplate.event.set 3 "input_3" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with entry := "wrong-root" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with
    event := queryTemplate.event.set 1 "wrong-definition" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with
    event := queryTemplate.event.set 4 "random.other/0" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with
    event := queryTemplate.event.set 5 "private-coins" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with
    event := queryTemplate.event.set 6 "role00000000" } = false := by decide +kernel
example : valid snapshot context { queryTemplate with
    steps := queryTemplate.steps.map fun step => { step with protocol := "wrong-caller" } } = false := by
  decide +kernel
example : valid snapshot (context.mapReplacement (fun replacement => { replacement with service := 0 })) queryTemplate = false := by decide +kernel
example : valid snapshot context { messageTemplate with
    event := messageTemplate.event.set 4 "role00000001" } = false := by decide +kernel
example : valid snapshot context { messageTemplate with
    event := messageTemplate.event.set 3 "wrong-schema" } = false := by decide +kernel

namespace RoleSubstitution
open Zkc.Source.Structured

-- A focused source-path fixture swaps the callee's roles and moves the
-- selected service from root input 2 to child input 0. It tests source alias
-- resolution, not admission of a new cryptographic domain.
private def child : Function :=
  ⟨"Child", .protocol, .privateDef, [.service "random.F/0"], [],
    some ⟨["P", "V"], [["P"]], []⟩, [], some (.protocol ⟨"Child", []⟩),
    .block [.instruction (.draw "P" "F") [0] [.field "F"] [] "q"] (.ret [])⟩

private def parent (swapped : Bool) : Function :=
  ⟨"Root", .protocol, .publicDef, [.field "F", .field "F", .service "random.F/0"], [],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"], ["V"]], []⟩, [], some (.protocol ⟨"Root", []⟩),
    .block [.instruction (.protocolApply "Child" (if swapped then ["V", "P"] else ["P", "V"]))
      [2] [] [] "call"] (.ret [])⟩

private def source (swapped : Bool) : Snapshot :=
  { snapshot with entry := "Root", definitions := [.function (parent swapped), .function child] }

private def rootContext : Context :=
  Context.fiatShamir "Root" (["P", "V"]) 0 1 2 "random.F/0" (some (.draw "F")) "suite" ([("call.q", "delivery")])

private def occurrence : Template :=
  ⟨"Root", [⟨"apply", "Root", "call"⟩], ["query", "Child", "q", "input_0", "random.F/0", "draw", "V"]⟩

example : valid (source true) rootContext occurrence = true := by decide +kernel
example : valid (source false) rootContext occurrence = false := by decide +kernel
example : valid (source true) rootContext { occurrence with event := occurrence.event.set 6 "P" } = false := by
  decide +kernel

end RoleSubstitution
end Tests.SourceOccurrences

namespace Tests.CompiledSourceOccurrences
open Zkc.Construction

private abbrev original := ZkcExamples.Construction.SchnorrProof.participant
private abbrev imported := ZkcExamples.Construction.SchnorrProof.imported
private abbrev context := ZkcExamples.Construction.SchnorrProof.context

-- The event remains syntactically a query but names the wrong source input.
-- Projection and nominal occurrence formatting alone cannot authenticate it.
private def wrongSourcePort : Participant := { original with
  instructions := original.instructions.map fun instruction =>
    match instruction.operation with
    | .challenge suite field template =>
        let changed : Template := { template with event := template.event.set 3 "input_0" }
        { instruction with operation := .challenge suite field changed }
    | _ => instruction }

private def inventedPath : Participant := { original with
  instructions := original.instructions.map fun instruction =>
    match instruction.operation with
    | .challenge suite field template =>
        let changed : Template := { template with steps := [⟨"unknown", template.entry, "invented"⟩] }
        { instruction with operation := .challenge suite field changed }
    | _ => instruction }

example : checkCompiled imported original = .ok () := by decide +kernel
example : checkCompiled imported wrongSourcePort = .error "construction-source-occurrence" := by
  decide +kernel
example : checkCompiled imported inventedPath = .error "construction-source-occurrence" := by
  decide +kernel

end Tests.CompiledSourceOccurrences
