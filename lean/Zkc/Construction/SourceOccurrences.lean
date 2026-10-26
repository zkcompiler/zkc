module

public import Zkc.Construction.Structured

@[expose] public section

/-! Exact source ownership of retained occurrence templates. Event definitions
and service ports are local to a callee; participant names and selected service
authority are transported along applications. Repeat captures preserve their
source input position. This is a structural admission check, not native-byte
correspondence or a second protocol execution semantics. -/

set_option autoImplicit false
namespace Zkc.Construction.SourceOccurrences
open Zkc.Source

structure Port where
  localInput : Nat
  rootInput : Nat
  deriving DecidableEq, Repr

abbrev Ports := List (Option Port)

structure Frame where
  definition : Structured.Function
  body : Structured.Block
  roles : List (String × String)
  ports : Ports

def function (snapshot : Structured.Snapshot) (name : String) : Option Structured.Function :=
  match snapshot.definitions.find? (·.name == name) with
  | some (.function value) => if value.kind = .protocol then some value else none
  | _ => none

def operands (ports : Ports) (indices : List Nat) : Option Ports := indices.mapM (ports[·]?)

/-- Restricting visibility preserves the identity of a borrowed service. No
arithmetic or helper result is silently promoted into a service capability. -/
def results (descriptor : Structured.Descriptor) (arguments : Ports) (types : List Structured.Ty) : Ports :=
  match descriptor, arguments, types with
  | .restrict _, [port], [_] => [port]
  | _, _, _ => types.map fun _ => none

/-- Locate the exact source site while carrying only static service aliases.
SSA results are prepended in the structured export's existing convention. -/
def atSite (site : String) : List Structured.Instruction → Ports → Option (Structured.Instruction × Ports)
  | [], _ => none
  | instruction@(.instruction descriptor indices types _ ownSite) :: rest, ports => do
      let arguments ← operands ports indices
      if ownSite = site then return (instruction, arguments)
      atSite site rest (results descriptor arguments types ++ ports)

def frameAt (frame : Frame) (site : String) : Option (Structured.Instruction × Ports) :=
  atSite site frame.body.topLevelInstructions frame.ports

def root (snapshot : Structured.Snapshot) (context : Context) : Option Frame := do
  let definition ← function snapshot context.entry
  let interface ← definition.interface
  if snapshot.entry ≠ context.entry ∨ interface.roles ≠ context.roles then none
  else some ⟨definition, definition.body, interface.roles.map fun role => (role, role),
    (List.range definition.inputs.length).map fun index => some ⟨index, index⟩⟩

/-- A step is resolved against the source operation at that exact path. Both
local and root service identities are retained across the call boundary. -/
def descend (snapshot : Structured.Snapshot) (frame : Frame) (step : Step) : Option Frame := do
  if step.protocol ≠ frame.definition.name then none else do
    let (instruction, arguments) ← frameAt frame step.site
    match step.kind, instruction with
    | "apply", .instruction (.protocolApply name roles) _ _ [] _ => do
        let child ← function snapshot name
        let interface ← child.interface
        if interface.roles.length ≠ roles.length ∨ child.inputs.length ≠ arguments.length then none
        else do
          let mapped ← roles.mapM (frame.roles.lookup ·)
          return ⟨child, child.body, interface.roles.zip mapped,
            arguments.zipIdx.map fun (port, index) => port.map fun origin => ⟨index, origin.rootInput⟩⟩
    | "repeat", .instruction (.protocolRepeat _ _ _ _) _ _ [.region inputs _ body] _ =>
        let ports := none :: arguments.drop 1
        if inputs.length = ports.length then some { frame with body := body, ports := ports } else none
    | _, _ => none

def follow (snapshot : Structured.Snapshot) : List Step → Frame → Option Frame
  | [], frame => some frame
  | step :: rest, frame => descend snapshot frame step >>= follow snapshot rest

/-- Reconstruct the full retained event from its source occurrence. Draws must
use the selected root service, even if the local input number differs. -/
def event (context : Context) (frame : Frame) (site : String) : Option (List String) := do
  let (instruction, arguments) ← frameAt frame site
  match instruction with
  | .instruction (.exchange sender receiver) _ _ [] _ => do
      let sender ← frame.roles.lookup sender
      let receiver ← frame.roles.lookup receiver
      return ["message", frame.definition.name, site, site, sender, receiver]
  | .instruction (.draw owner field) _ _ [] _ => do
      let [some port] := arguments | none
      let some (.service contract) := frame.definition.inputs[port.localInput]? | none
      let owner ← frame.roles.lookup owner
      if some port.rootInput ≠ context.service ∨ contract ≠ context.contract ∨
          context.request ≠ some (.draw field) ∨ owner ≠ context.role context.validator then none
      else some ["query", frame.definition.name, site, "input_" ++ decimal port.localInput,
        contract, "draw", owner]
  | _ => none

def expected (snapshot : Structured.Snapshot) (context : Context) (template : Template) : Option (List String) := do
  if template.entry ≠ context.entry then none else do
    let initial ← root snapshot context
    let frame ← follow snapshot template.steps initial
    let site ← template.event[2]?
    event context frame site

def valid (snapshot : Structured.Snapshot) (context : Context) (template : Template) : Bool :=
  expected snapshot context template == some template.event

theorem valid_iff (snapshot : Structured.Snapshot) (context : Context) (template : Template) :
    valid snapshot context template = true ↔ expected snapshot context template = some template.event := by
  simp [valid]

/-- The complete native service interface, including unused capabilities. The
root is a source input, while the native position counts role-local data and
services after the selected validator services have been removed. -/
def servicePorts (snapshot : Structured.Snapshot) (policy : Policy) (owner : String) :
    Option (List ServicePort) := do
  let (inputs, interface) ← entryInterface snapshot
  if policy.entry ≠ snapshot.entry ∨ owner ∉ interface.roles then none else do
    let roots := ((inputs.zip interface.inputScopes).zipIdx.filter fun ((_, scope), index) =>
      scope.contains owner && !(owner == policy.validator && policy.services.contains index))
    let ports ← roots.zipIdx.mapM fun (((ty, scope), root), input) =>
      match ty with
      | .service contract =>
          if scope = [owner] then
            some (some (⟨"service_" ++ decimal input, owner, root, input, contract⟩ : ServicePort))
          else none
      | _ => some none
    return ports.filterMap id

/-- Resolve a local draw independently of the selected public challenge. The
same root survives restrictions, application substitution and repeat captures. -/
def localEvent (snapshot : Structured.Snapshot) (context : Context) (port : ServicePort)
    (request : Request) (template : Template) : Option (List String) := do
  if template.entry ≠ context.entry ∨ port.owner ≠ context.role context.producer then none else do
    let initial ← root snapshot context
    let frame ← follow snapshot template.steps initial
    let site ← template.event[2]?
    let (instruction, arguments) ← frameAt frame site
    let .instruction (.draw owner field) _ [.field result] [] _ := instruction | none
    let [some source] := arguments | none
    let some (.service contract) := frame.definition.inputs[source.localInput]? | none
    let owner ← frame.roles.lookup owner
    let some (.service rootContract) := initial.definition.inputs[source.rootInput]? | none
    let interface ← initial.definition.interface
    if source.rootInput ≠ port.root ∨ contract ≠ port.contract ∨ rootContract ≠ contract ∨
        interface.inputScopes[source.rootInput]? ≠ some [owner] ∨ owner ≠ port.owner ∨
        request ≠ .draw field ∨ result ≠ field ∨ contract ≠ "random." ++ field ++ "/0" then none
    else some ["query", frame.definition.name, site, "input_" ++ decimal source.localInput,
      contract, "draw", owner]

def localValid (snapshot : Structured.Snapshot) (context : Context) (port : ServicePort)
    (request : Request) (template : Template) : Bool :=
  localEvent snapshot context port request template == some template.event

theorem localValid_iff (snapshot : Structured.Snapshot) (context : Context) (port : ServicePort)
    (request : Request) (template : Template) :
    localValid snapshot context port request template = true ↔
      localEvent snapshot context port request template = some template.event := by
  simp [localValid]

/-- Native loop sites include the application prefix at the point of the
repeat, rather than the prefix of a later application inside that repeat. -/
def repeatSites (template : Template) : List String :=
  (template.steps.foldl (fun (state : Option String × List String) step =>
    if step.kind = "apply" then
      (some (Structured.qualifyProtocolSite state.1 step.site), state.2)
    else if step.kind = "repeat" then
      (state.1, state.2 ++ [Structured.qualifyProtocolSite state.1 step.site])
    else state) (none, [])).2

mutual
/-- Every transcript operation, including nested loop bodies, must retain its
actual source event. The construction rule separately checks sequencing and
dynamic coordinate provenance. -/
def instruction (snapshot : Structured.Snapshot) (context : Context) (ports : List ServicePort)
    (loops : List String) : Instruction → Bool
  | ⟨operation, _, _, body⟩ =>
      (match operation with
       | .observe _ template | .challenge _ _ template => valid snapshot context template
       | .localService port request template _ =>
           ports.contains port && localValid snapshot context port request template &&
             repeatSites template == loops
       | _ => true) && instructions snapshot context ports
         (match operation with | .loop site .. => loops ++ [site] | _ => loops) body

def instructions (snapshot : Structured.Snapshot) (context : Context) (ports : List ServicePort)
    (loops : List String) : List Instruction → Bool
  | [] => true
  | first :: rest => instruction snapshot context ports loops first && instructions snapshot context ports loops rest
end

def check (snapshot : Structured.Snapshot) (context : Context) (participant : Participant) : Except String Unit :=
  if instructions snapshot context participant.servicePorts [] participant.instructions then .ok ()
  else .error "construction-source-occurrence"

end Zkc.Construction.SourceOccurrences
