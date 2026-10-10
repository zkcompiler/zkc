import Tools.Interactive.GenericModule
import Tools.Interactive.LocalValidation
import Tools.Interactive.Projection

/-! Combine independently formed generic locals with common-control projection.
Source configuration names can map many-to-one to checked candidate functions.
The resulting port maps retain original source names for host-side policy. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic
open Lean (Json)

private def physicalType (physical : Bool) (spelling : Ty) : Result Ty := do
  let logical ← Bindings.valueType false spelling
  return (if physical then { logical with representation := Bindings.defaultRepresentation logical.kind logical.identity }
    else logical).spelling

private def physicalBody (physical : Bool) : Nat → List Instruction → Result (List Instruction)
  | 0, _ => .error "body-depth-limit"
  | depth + 1, body => body.mapM fun instruction => do
      match instruction with
      | .receive site schema peer name ty => return .receive site schema peer name (← physicalType physical ty)
      | .loop site count carried captures nested outputs =>
          return .loop site count carried captures (← physicalBody physical depth nested) outputs
      | other => return other

private def physicalParticipant (physical : Bool) (participant : Participant) : Result Participant := do
  return { participant with
    arguments := ← participant.arguments.mapM fun (name, ty) => do return (name, ← physicalType physical ty)
    results := ← participant.results.mapM (physicalType physical)
    body := ← physicalBody physical limits.depth participant.body }

structure LocalOccurrence where
  site : Name
  configuration : Name
  function : Name
  deriving BEq, Repr

private def sameBody (locals : List LocalCorrespondence) : Nat → List Instruction → List Instruction → Result (List LocalOccurrence)
  | 0, _, _ => .error "body-depth-limit"
  | depth + 1, source, candidate => do
      ensure (source.length == candidate.length) "participant-body-length"
      let mut occurrences := []
      for (expected, actual) in source.zip candidate do
        match expected, actual with
        | .localCall site owner function inputs outputs, .localCall s o f i r =>
            ensure (site == s && owner == o && inputs == i && outputs == r) "participant-local-correspondence"
            ensure (locals.any fun pair => pair.configuration == function && pair.function == f)
              "participant-local-selection"
            occurrences := occurrences ++ [⟨site, function, f⟩]
        | .loop site count carried captures body outputs, .loop s c args caps nested results =>
            ensure (site == s && count == c && carried == args && captures == caps && outputs == results)
              "participant-loop-correspondence"
            occurrences := occurrences ++ (← sameBody locals depth body nested)
        | _, _ => ensure (expected == actual) "participant-instruction-correspondence"
      return occurrences

structure PortMap where
  binding : Name
  role : Name
  participant : Name
  arguments : List (Name × Name)
  deriving BEq, Repr

structure Correspondence where
  prepared : Prepared
  ports : List PortMap
  calls : List (Name × Name × LocalOccurrence)

/-- An executable structural checker. The raw decoder and native execution are
not covered by a theorem merely because this function returns successfully. -/
def validate (json candidateJson : Json) : Result Correspondence := do
  let prepared ← prepareSource json
  let candidate ← Explicit.candidateLocals candidateJson
  let participants ← (← Decode.array candidate.participants limits.definitions).mapM
    (fun j => Decode.participant j (Explicit.typeName candidate.physical))
  let entries ← (← Decode.array candidate.entries limits.definitions).mapM fun j => do
    let [.str "entry", name, roles] ← Decode.array j | throw "invalid-entry"
    return (← Decode.name name, ← Decode.pairs (fun j => Decode.name j) (fun j => Decode.name j 512) roles)
  let count := (candidate.functions.map fun f => instructionCount limits.depth (f.code.body.getD [])).sum +
    (participants.map fun p => instructionCount limits.depth p.body).sum
  ensure (count ≤ limits.instructions) "module-instruction-limit"
  let mut locals := []
  let mut attempts := 0
  let .explicit sourceBindings := prepared.source.environment
  for function in prepared.functions do
    for actual in candidate.functions do
      if actual.origin == function.origin then
        attempts := attempts + 1
        ensure (attempts ≤ 32768) "local-correspondence-work-limit"
        if let .ok checked := validateClosed function sourceBindings candidate actual.code.name then
          locals := locals ++ [checked]
    ensure (locals.any fun pair => pair.configuration == function.code.name) "source-local-unmatched"
  for actual in candidate.functions do
    ensure (locals.any fun pair => pair.function == actual.code.name) "candidate-local-unmatched"
  let (logicalParticipants, expectedEntries) ← projectControl prepared.source
  let expected ← logicalParticipants.mapM (physicalParticipant candidate.physical)
  let symbols := participants.map fun p => (p.name, participantKey p.binding p.role)
  let expectedSymbols := expected.map fun p => (p.name, participantKey p.binding p.role)
  ensure (unique (symbols.map Prod.fst) &&
    unique (symbols.map Prod.fst ++ candidate.functions.map (fun f => f.code.name) ++ candidate.bindings.map OperationBinding.name))
    "duplicate-participant-symbol"
  ensure (exactKeys (symbols.map fun p => (p.2, ())) (expectedSymbols.map fun p => (p.2, ()))) "candidate-participants"
  let mut ports := []
  let mut calls := []
  for actual in participants do
    let key := participantKey actual.binding actual.role
    let original ← lookup key (expected.map fun p => (participantKey p.binding p.role, p))
    let a ← normalizeParticipant symbols actual
    let e ← normalizeParticipant expectedSymbols original
    ensure ({ a with body := [] } == { e with body := [] }) "participant-signature-correspondence"
    let occurrences ← sameBody locals limits.depth e.body a.body
    calls := calls ++ occurrences.map (fun c => (actual.binding, actual.role, c))
    ports := ports ++ [⟨actual.binding, actual.role, actual.name,
      (original.arguments.map Prod.fst).zip (actual.arguments.map Prod.fst)⟩]
  ensure (exactKeys entries expectedEntries) "candidate-entries"
  for (name, roles) in entries do
    let expected ← lookup name expectedEntries
    ensure (exactKeys roles expected) "entry-roles"
    for (role, symbol) in roles do
      ensure ((← lookup symbol symbols) == (← lookup (← lookup role expected) expectedSymbols))
        "entry-participant-correspondence"
  return ⟨prepared, ports, calls⟩

end Tools.Interactive.Generic
