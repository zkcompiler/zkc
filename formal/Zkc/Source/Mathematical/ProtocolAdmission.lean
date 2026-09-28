import Zkc.Source.Mathematical.Protocol
import Zkc.Source.Mathematical.FormationLimits

/-! Admission of a resolved ordered body into intrinsic syntax with exact
erasure. Source declaration resolution supplies the algebra, finite call scope
and service identities; this module checks all value and capability uses.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

inductive Raw (Role : Type) (vocabulary : Vocabulary) where
  | ret (values : List Nat)
  | pure (captures : List Nat) (region : Graph.Raw vocabulary.Op vocabulary.Count)
      (next : Raw Role vocabulary)
  | local (site : Nat) (owner : Role) (op : vocabulary.Local)
      (capabilities arguments : List Nat) (next : Raw Role vocabulary)
  | query (site : Nat) (owner : Role) (capability : Nat) (arguments : List Nat)
      (next : Raw Role vocabulary)
  | guard (site : Nat) (owner : Role) (condition : Nat) (next : Raw Role vocabulary)
  | message (site : Nat) (wire : (ty : vocabulary.Ty) × vocabulary.Wire ty)
      (sender receiver : Role) (value : Nat) (next : Raw Role vocabulary)
  | invoke (site callee : Nat) (capabilities arguments : List Nat) (next : Raw Role vocabulary)
  | repeat (site : Nat) (count : vocabulary.Count) (carried : List (Port Role vocabulary.Ty))
      (initial captures : List Nat) (body next : Raw Role vocabulary)
  | stop (site : Nat) (owner : Role) (reason : PIR.Stop)

inductive Error where
  | graph (reason : Graph.Error)
  | resource | depth | site | owner | permission | service | alias | sender | count
  deriving DecidableEq, Repr

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}

def bindingIndices {Γ ports : List (Port Role vocabulary.Ty)} : Bindings Γ ports → List Nat
  | .nil => []
  | .cons value rest => value.operand.index :: bindingIndices rest

def selectReference [DecidableEq vocabulary.Ty] (Γ : List (Port Role vocabulary.Ty))
    (port : Port Role vocabulary.Ty) (index : Nat) :
    Except Error { value : Reference Γ port // value.operand.index = index } := do
  let selected ← (Graph.select Γ index).mapError Error.graph
  if same : selected.ty.ty = port.ty then
    if covers : ∀ role ∈ port.roles, role ∈ selected.ty.roles then
      let value : Reference Γ port := ⟨selected.ty.roles,
        Graph.castVariable (algebra := vocabulary.toAlgebra) same selected.value, covers⟩
      return ⟨value, by simpa [value] using selected.erasure⟩
    else throw .permission
  else throw (.graph .type)

def selectBindings [DecidableEq vocabulary.Ty] (Γ : List (Port Role vocabulary.Ty)) :
    (ports : List (Port Role vocabulary.Ty)) → (indices : List Nat) →
    Except Error { bindings : Bindings Γ ports // bindingIndices bindings = indices }
  | [], [] => return ⟨.nil, rfl⟩
  | port :: ports, index :: indices => do
      let first ← selectReference Γ port index
      let rest ← selectBindings Γ ports indices
      return ⟨.cons first.val rest.val, by simp [bindingIndices, first.property, rest.property]⟩
  | _, _ => throw (.graph .arity)

private def castCapability {capabilities : List (Capability Role vocabulary.Service)}
    {a b : vocabulary.Service} {roles root} (same : a = b)
    (value : Var capabilities ⟨⟨a, roles⟩, root⟩) : Var capabilities ⟨⟨b, roles⟩, root⟩ :=
  same ▸ value

omit [DecidableEq Role] in
private theorem castCapability_index {capabilities : List (Capability Role vocabulary.Service)}
    {a b : vocabulary.Service} {roles root} (same : a = b)
    (value : Var capabilities ⟨⟨a, roles⟩, root⟩) :
    (castCapability same value).index = value.index := by cases same; rfl

def selectCapability [DecidableEq vocabulary.Service]
    (capabilities : List (Capability Role vocabulary.Service))
    (required : Permission Role vocabulary.Service) (index : Nat) :
    Except Error { value : CapabilityReference capabilities required // value.operand.index = index } := do
  let selected ← (Graph.select capabilities index).mapError Error.graph
  if same : selected.ty.service = required.service then
    if covers : ∀ role ∈ required.roles, role ∈ selected.ty.roles then
      let value : CapabilityReference capabilities required :=
        ⟨selected.ty.roles, selected.ty.root, castCapability same selected.value, covers⟩
      return ⟨value, by simpa [value, castCapability_index] using selected.erasure⟩
    else throw .permission
  else throw .service

def selectCapabilities [DecidableEq vocabulary.Service]
    (capabilities : List (Capability Role vocabulary.Service)) :
    (required : List (Permission Role vocabulary.Service)) → (indices : List Nat) →
    Except Error { bindings : CapabilityBindings capabilities required // bindings.indices = indices }
  | [], [] => return ⟨.nil, rfl⟩
  | port :: ports, index :: indices => do
      let first ← selectCapability capabilities port index
      let rest ← selectCapabilities capabilities ports indices
      return ⟨.cons first.val rest.val,
        by simp [CapabilityBindings.indices, first.property, rest.property]⟩
  | _, _ => throw (.graph .arity)

variable {parties : List Role} {capabilities : List (Capability Role vocabulary.Service)}
  {scope : List (Signature Role vocabulary)}

def Program.erase {Γ results start finish} :
    Program parties vocabulary capabilities scope Γ results start finish → Raw Role vocabulary
  | .ret values => .ret (bindingIndices values)
  | .pure captures region next => .pure (Graph.operandIndices captures) region.erase next.erase
  | .local owner _ op bindings arguments _ next =>
      .local start owner op bindings.indices (Graph.inputIndices arguments) next.erase
  | .query owner _ capability _ arguments _ next =>
      .query start owner capability.index (Graph.inputIndices arguments) next.erase
  | .guard owner _ condition next => .guard start owner condition.operand.index next.erase
  | .message schema sender receiver _ _ _ value next =>
      .message start ⟨_, schema⟩ sender receiver value.operand.index next.erase
  | .invoke callee _ binding arguments next =>
      .invoke start callee.index binding.indices (bindingIndices arguments) next.erase
  | .repeat (carried := carried) count initial capture body next =>
      .repeat start count carried (bindingIndices initial) (Graph.operandIndices capture) body.erase next.erase
  | .stop owner _ reason => .stop start owner reason

structure Formed (parties : List Role) (vocabulary : Vocabulary)
    (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (Γ results : List (Port Role vocabulary.Ty)) (start : Nat) (raw : Raw Role vocabulary) where
  finish : Nat
  program : Program parties vocabulary capabilities scope Γ results start finish
  erasure : program.erase = raw

/-- Admission counters retained by an installed vocabulary. Generic callers
can omit them and use bounded measurement at each signature boundary. -/
structure SignatureMeasurements (nodes height : vocabulary.Ty → Nat) where
  graph : (operation : vocabulary.Op) → Option
    (SignatureMeasurement nodes height (vocabulary.arguments operation) (vocabulary.result operation)) := fun _ => none
  localOperation : (operation : vocabulary.Local) → Option
    (SignatureMeasurement nodes height (vocabulary.localArguments operation) (vocabulary.localResult operation)) := fun _ => none
  service : (service : vocabulary.Service) → Option
    (SignatureMeasurement nodes height (vocabulary.serviceArguments service) (vocabulary.serviceResult service)) := fun _ => none
  wire : {type : vocabulary.Ty} → vocabulary.Wire type →
    Option (TypeMeasurement nodes height type) := fun _ => none

/-- The allowance is body depth plus one. Continuations retain it, nested
repeat bodies spend two levels, and each pure region gets its own allowance. -/
def formMeasured [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (parties : List Role) (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra)
    (countValid : vocabulary.Count → Bool)
    (fuel : Nat) (Γ results : List (Port Role vocabulary.Ty))
    (measured : Graph.MeasuredPorts capacity Γ) (measuredResults : Graph.MeasuredPorts capacity results)
    (start : Nat) (raw : Raw Role vocabulary) (signatures : SignatureMeasurements capacity.nodes capacity.height := {}) :
    Except Error (Formed parties vocabulary capabilities scope Γ results start raw) :=
  match fuel with
  | 0 => throw .depth
  | fuel + 1 => do
      match hraw : raw with
      | .ret indices =>
          let values ← selectBindings Γ results indices
          return ⟨start, .ret values.val, by simp [Program.erase, values.property, hraw]⟩
      | .pure indices region next =>
          let captures ← (Graph.selectOperands Γ indices).mapError Error.graph
          let captured := Operands.eval (fun v => measured.get v) captures.values
          let graph ← (Graph.decodeMeasured parties capacity countValid (FormationLimits.regionDepth + 1)
            captures.ports captured region signatures.graph).mapError Error.graph
          let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
            (graph.ports ++ Γ) results (Graph.appendMeasured graph.measured measured) measuredResults start next signatures
          return ⟨tail.finish, .pure captures.values graph.region tail.program,
            by simp [Program.erase, captures.erasure, graph.erasure, tail.erasure, hraw]⟩
      | .local site owner op indices arguments next =>
          if siteEq : start = site then
            if owned : owner ∈ parties then
              let some result := capacity.measureSignatureResult (vocabulary.localArguments op)
                (vocabulary.localResult op) (signatures.localOperation op) | throw .resource
              let bindings ← selectCapabilities capabilities (localPermissions owner op) indices
              let args ← (Graph.selectInputs Γ (vocabulary.localArguments op) arguments).mapError Error.graph
              if available : owner ∈ Inputs.available parties args.val then
                let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
                  (⟨[owner], vocabulary.localResult op⟩ :: Γ) results (.cons result measured) measuredResults (start + 1) next signatures
                return ⟨tail.finish, .local owner owned op bindings.val args.val available tail.program,
                  by simp [Program.erase, siteEq, bindings.property, args.property, tail.erasure, hraw]⟩
              else throw .permission
            else throw .owner
          else throw .site
      | .query site owner index arguments next =>
          if siteEq : start = site then
            if owned : owner ∈ parties then
              let cap ← (Graph.select capabilities index).mapError Error.graph
              if permitted : owner ∈ cap.ty.roles then
                let some result := capacity.measureSignatureResult (vocabulary.serviceArguments cap.ty.service)
                  (vocabulary.serviceResult cap.ty.service) (signatures.service cap.ty.service) | throw .resource
                let args ← (Graph.selectInputs Γ (vocabulary.serviceArguments cap.ty.service) arguments).mapError Error.graph
                if available : owner ∈ Inputs.available parties args.val then
                  let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
                    (⟨[owner], vocabulary.serviceResult cap.ty.service⟩ :: Γ) results (.cons result measured) measuredResults (start + 1) next signatures
                  return ⟨tail.finish, .query owner owned cap.value permitted args.val available tail.program,
                    by simp [Program.erase, siteEq, cap.erasure, args.property, tail.erasure, hraw]⟩
                else throw .permission
              else throw .permission
            else throw .owner
          else throw .site
      | .guard site owner index next =>
          if siteEq : start = site then
            if owned : owner ∈ parties then
              let some _ := capacity.measure vocabulary.condition | throw .resource
              let condition ← selectReference Γ ⟨[owner], vocabulary.condition⟩ index
              let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1) Γ results measured measuredResults (start + 1) next signatures
              return ⟨tail.finish, .guard owner owned condition.val tail.program,
                by simp [Program.erase, siteEq, condition.property, tail.erasure, hraw]⟩
            else throw .owner
          else throw .site
      | .message site ⟨ty, wire⟩ sender receiver index next =>
          if siteEq : start = site then
            if sending : sender ∈ parties then
              if receiving : receiver ∈ parties then
                if different : sender ≠ receiver then
                  let some result := (match signatures.wire wire with
                    | some measured => some (capacity.boundary measured)
                    | none => capacity.measure ty) | throw .resource
                  let value ← selectReference Γ ⟨[sender], ty⟩ index
                  let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
                    (⟨messageRoles parties sender receiver, ty⟩ :: Γ) results (.cons result measured) measuredResults (start + 1) next signatures
                  return ⟨tail.finish, .message wire sender receiver sending receiving different value.val tail.program,
                    by simp [Program.erase, siteEq, value.property, tail.erasure, hraw]⟩
                else throw .sender
              else throw .owner
            else throw .owner
          else throw .site
      | .invoke site index indices arguments next =>
          if siteEq : start = site then
            let callee ← (Graph.select scope index).mapError Error.graph
            if participates : ∀ role ∈ callee.ty.parties, role ∈ parties then
              let some _ := Graph.measurePorts capacity callee.ty.arguments | throw .resource
              let some outputSizes := Graph.measurePorts capacity callee.ty.results | throw .resource
              let bindings ← selectCapabilities capabilities callee.ty.capabilities indices
              let args ← selectBindings Γ callee.ty.arguments arguments
              let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
                (callee.ty.results ++ Γ) results (Graph.appendMeasured outputSizes measured) measuredResults (start + 1) next signatures
              return ⟨tail.finish, .invoke callee.value participates bindings.val args.val tail.program,
                by simp [Program.erase, siteEq, callee.erasure, bindings.property, args.property, tail.erasure, hraw]⟩
            else throw .owner
          else throw .site
      | .repeat site count carried initial indices body next =>
          if siteEq : start = site then
            if !countValid count then throw .count
            let some carriedSizes := Graph.measurePorts capacity carried | throw .resource
            let some index := capacity.measure (vocabulary.index count) | throw .resource
            let initial ← selectBindings Γ carried initial
            let captures ← (Graph.selectOperands Γ indices).mapError Error.graph
            let captured := Operands.eval (fun v => measured.get v) captures.values
            let nested ← formMeasured parties capabilities scope capacity countValid (fuel - 1)
              (⟨parties, vocabulary.index count⟩ :: (carried ++ captures.ports)) carried
              (.cons index (Graph.appendMeasured carriedSizes captured)) carriedSizes (start + 1) body signatures
            let tail ← formMeasured parties capabilities scope capacity countValid (fuel + 1)
              (carried ++ Γ) results (Graph.appendMeasured carriedSizes measured) measuredResults nested.finish next signatures
            return ⟨tail.finish, .repeat count initial.val captures.values nested.program tail.program,
              by simp [Program.erase, siteEq, initial.property, captures.erasure, nested.erasure, tail.erasure, hraw]⟩
          else throw .site
      | .stop site owner reason =>
          if siteEq : start = site then
            if owned : owner ∈ parties then
              return ⟨start + 1, .stop owner owned reason, by simp [Program.erase, siteEq, hraw]⟩
            else throw .owner
          else throw .site

  termination_by structural raw

/-- External context and result types are measured once. Recursive formation
propagates certified measurements as bindings and scopes change. -/
def form [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (parties : List Role) (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra) (countValid : vocabulary.Count → Bool)
    (fuel : Nat) (Γ results : List (Port Role vocabulary.Ty)) (start : Nat) (raw : Raw Role vocabulary)
    (signatures : SignatureMeasurements capacity.nodes capacity.height := {}) :
    Except Error (Formed parties vocabulary capabilities scope Γ results start raw) := do
  if fuel == 0 then throw .depth
  let some measured := Graph.measurePorts capacity Γ | throw .resource
  let some measuredResults := Graph.measurePorts capacity results | throw .resource
  formMeasured parties capabilities scope capacity countValid fuel Γ results measured measuredResults start raw signatures

/-- Closed-body admission retains a proof for every recorded root requirement.
The same `form` checker supplies symbolic template formation without treating
parameter ordinals as evidence of distinct concrete state. -/
structure Decoded (parties : List Role) (vocabulary : Vocabulary)
    (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (Γ results : List (Port Role vocabulary.Ty)) (start : Nat) (raw : Raw Role vocabulary)
    extends Formed parties vocabulary capabilities scope Γ results start raw where
  roots : program.rootsValid = true

def Formed.dischargeRoots {Γ results start raw}
    (formed : Formed parties vocabulary capabilities scope Γ results start raw) :
    Except Error (Decoded parties vocabulary capabilities scope Γ results start raw) :=
  if roots : formed.program.rootsValid = true then .ok ⟨formed, roots⟩
  else .error .alias

def decode [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (parties : List Role) (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra) (countValid : vocabulary.Count → Bool)
    (fuel : Nat) (Γ results : List (Port Role vocabulary.Ty)) (start : Nat) (raw : Raw Role vocabulary)
    (signatures : SignatureMeasurements capacity.nodes capacity.height := {}) :
    Except Error (Decoded parties vocabulary capabilities scope Γ results start raw) := do
  let formed ← form parties capabilities scope capacity countValid fuel Γ results start raw signatures
  formed.dischargeRoots

theorem decode_erases [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (parties : List Role) (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra) (countValid : vocabulary.Count → Bool)
    {signatures : SignatureMeasurements capacity.nodes capacity.height}
    {fuel Γ results start raw result}
    (_accepted : decode parties capabilities scope capacity countValid fuel Γ results start raw signatures = .ok result) :
    result.program.erase = raw := result.erasure

end Zkc.Source.Mathematical.Protocol
