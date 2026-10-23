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
      if port.rootInput ≠ context.service ∨ contract ≠ context.contract ∨
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

mutual
/-- Every transcript operation, including nested loop bodies, must retain its
actual source event. The construction rule separately checks sequencing and
dynamic coordinate provenance. -/
def instruction (snapshot : Structured.Snapshot) (context : Context) : Instruction → Bool
  | ⟨operation, _, _, body⟩ =>
      (match operation with
       | .observe _ template | .challenge _ _ template => valid snapshot context template
       | _ => true) && instructions snapshot context body

def instructions (snapshot : Structured.Snapshot) (context : Context) : List Instruction → Bool
  | [] => true
  | first :: rest => instruction snapshot context first && instructions snapshot context rest
end

def check (snapshot : Structured.Snapshot) (context : Context) (participant : Participant) : Except String Unit :=
  if instructions snapshot context participant.instructions then .ok ()
  else .error "construction-source-occurrence"

end Zkc.Construction.SourceOccurrences
