import Zkc.Source.Mathematical.AdmissionWork
import Zkc.Source.Mathematical.GraphResolution
import Zkc.Source.Mathematical.ProtocolAdmission
import Zkc.Source.Mathematical.RoleResolution

/-! Carrier bodies with certified declaration selection and exact source
retention. Definition admission owns type/role substitutions and closed call
selection. The intrinsic checker then checks the selected signatures, value
uses, capability roots, capture boundaries and effect sites.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ProtocolResolution

structure WireUse where
  wire : Raw.Reference .wire
  statics : List Static.Raw

structure CallUse where
  definition : Raw.Reference .definition
  statics : List Static.Raw
  roles : List (Raw.Reference .role)
  capabilities : List (Raw.Reference .capabilityPort)
  deriving DecidableEq

structure Resolver (vocabulary : Protocol.Vocabulary) where
  roles : RoleResolution.Binding
  graph : GraphResolution.Resolver vocabulary.toAlgebra
  LocalValid : GraphResolution.OperationUse → vocabulary.Local → Prop
  WireValid : WireUse → ((ty : vocabulary.Ty) × vocabulary.Wire ty) → Prop
  CallValid : CallUse → Nat → Prop
  PortValid : Raw.Port → Port Nat vocabulary.Ty → Prop
  localOperation : (source : GraphResolution.OperationUse) →
    StateT Nat (Except String) { op : vocabulary.Local // LocalValid source op }
  wire : (source : WireUse) →
    StateT Nat (Except String) { wire : (ty : vocabulary.Ty) × vocabulary.Wire ty // WireValid source wire }
  call : (source : CallUse) → StateT Nat (Except String) { index : Nat // CallValid source index }
  port : (source : Raw.Port) → StateT Nat (Except String) { port : Port Nat vocabulary.Ty // PortValid source port }

variable {vocabulary : Protocol.Vocabulary}

inductive Terminal (resolver : Resolver vocabulary) where
  | ret (values : List (Raw.Reference .value))
  | stop (site : Nat) (owner : RoleResolution.Use resolver.roles) (reason : PIR.Stop)

def Terminal.erase {resolver : Resolver vocabulary} : Terminal resolver → Raw.Terminal
  | .ret values => .ret values
  | .stop site owner reason => .stop site owner.source reason

def Terminal.lower {resolver : Resolver vocabulary} : Terminal resolver → Protocol.Raw Nat vocabulary
  | .ret values => .ret (values.map (·.index))
  | .stop site owner reason => .stop site owner.role reason

mutual
  inductive Step (resolver : Resolver vocabulary) where
    | pure (region : GraphResolution.Region resolver.graph)
    | local (site : Nat) (owner : RoleResolution.Use resolver.roles) (source : GraphResolution.OperationUse)
        (op : vocabulary.Local) (valid : resolver.LocalValid source op)
        (capabilities : List (Raw.Reference .capabilityPort)) (arguments : List (Raw.Reference .value))
    | query (site : Nat) (owner : RoleResolution.Use resolver.roles) (capability : Raw.Reference .capabilityPort)
        (arguments : List (Raw.Reference .value))
    | guard (site : Nat) (owner : RoleResolution.Use resolver.roles) (condition : Raw.Reference .value)
    | message (site : Nat) (source : WireUse) (wire : (ty : vocabulary.Ty) × vocabulary.Wire ty)
        (valid : resolver.WireValid source wire)
        (sender receiver : RoleResolution.Use resolver.roles) (value : Raw.Reference .value)
    | invoke (site : Nat) (source : CallUse) (callee : Nat) (valid : resolver.CallValid source callee)
        (arguments : List (Raw.Reference .value))
    | repeat (site : Nat) (source : Static.Raw) (count : vocabulary.Count)
        (valid : resolver.graph.CountValid source count)
        (carried : List ((raw : Raw.Port) × { port : Port Nat vocabulary.Ty // resolver.PortValid raw port }))
        (initial captures : List (Raw.Reference .value)) (body : Body resolver)
  inductive Body (resolver : Resolver vocabulary) where
    | mk (steps : List (Step resolver)) (terminal : Terminal resolver)
end

variable {resolver : Resolver vocabulary}

mutual
  def Step.erase : Step resolver → Raw.Step
    | .pure region => .pure region.erase
    | .local site owner source _ _ capabilities arguments =>
        .local site owner.source source.operation source.statics source.attributes capabilities arguments
    | .query site owner capability arguments => .query site owner.source capability arguments
    | .guard site owner condition => .guard site owner.source condition
    | .message site source _ _ sender receiver value => .message site source.wire source.statics sender.source receiver.source value
    | .invoke site source _ _ arguments =>
        .invoke site source.definition source.statics source.roles source.capabilities arguments
    | .repeat site source _ _ carried initial captures body =>
        .repeat site source (carried.map (·.1)) initial captures body.erase
  def Body.erase : Body resolver → Raw.Body
    | .mk steps terminal => .mk (steps.map Step.erase) terminal.erase
end

mutual
  def Step.lower (next : Protocol.Raw Nat vocabulary) : Step resolver → Protocol.Raw Nat vocabulary
    | .pure region => .pure region.captures region.lower next
    | .local site owner _ op _ capabilities arguments =>
        .local site owner.role op (capabilities.map (·.index)) (arguments.map (·.index)) next
    | .query site owner capability arguments => .query site owner.role capability.index (arguments.map (·.index)) next
    | .guard site owner condition => .guard site owner.role condition.index next
    | .message site _ wire _ sender receiver value => .message site wire sender.role receiver.role value.index next
    | .invoke site source callee _ arguments =>
        .invoke site callee (source.capabilities.map (·.index)) (arguments.map (·.index)) next
    | .repeat site _ count _ carried initial captures body =>
        .repeat site count (carried.map (·.2.val)) (initial.map (·.index)) (captures.map (·.index)) body.lower next
  def Body.lower : Body resolver → Protocol.Raw Nat vocabulary
    | .mk steps terminal => steps.foldr (fun step next => step.lower next) terminal.lower
end

inductive Error where
  | resource | depth | parties
  | selection (reason : String)
  | graph (reason : GraphResolution.Error)
  | protocol (reason : Protocol.Error)
  deriving Repr

abbrev Admission := StateT Nat (Except Error)

private def consume (amount : Nat := 1) : Admission Unit :=
  AdmissionWork.consume .resource amount

private def select {α : Type} (action : StateT Nat (Except String) α) : Admission α :=
  AdmissionWork.checked .resource Error.selection action

def terminal (resolver : Resolver vocabulary) (raw : Raw.Terminal) :
    Admission { result : Terminal resolver // result.erase = raw } := do
  match hraw : raw with
  | .ret values => return ⟨.ret values, by simp [Terminal.erase, hraw]⟩
  | .stop site owner reason =>
      let owner ← select (RoleResolution.resolve resolver.roles owner)
      return ⟨.stop site owner.val reason, by simp [Terminal.erase, owner.property, hraw]⟩

def ports (resolver : Resolver vocabulary) : (source : List Raw.Port) → Admission
    { result : List ((raw : Raw.Port) × { port : Port Nat vocabulary.Ty // resolver.PortValid raw port }) //
      result.map (·.1) = source }
  | [] => return ⟨[], rfl⟩
  | first :: rest => do
      consume
      let selected ← select (resolver.port first)
      let rest ← ports resolver rest
      return ⟨⟨first, selected⟩ :: rest.val, by simp [rest.property]⟩

mutual
  def step (resolver : Resolver vocabulary) (fuel : Nat) (raw : Raw.Step) :
      Admission { result : Step resolver // result.erase = raw } := do
    consume
    match hraw : raw with
    | .pure region =>
        let resolved ← fun available =>
          (GraphResolution.region resolver.graph (FormationLimits.regionDepth + 1) region available).mapError Error.graph
        return ⟨.pure resolved.val, by simp [Step.erase, resolved.property, hraw]⟩
    | .local site owner operation statics attributes capabilities arguments =>
        let _ ← AdmissionWork.length .resource statics
        let _ ← AdmissionWork.length .resource capabilities
        let _ ← AdmissionWork.length .resource arguments
        let owner ← select (RoleResolution.resolve resolver.roles owner)
        let selected ← select (resolver.localOperation ⟨operation, statics, attributes⟩)
        return ⟨.local site owner.val ⟨operation, statics, attributes⟩ selected.val selected.property capabilities arguments,
          by simp [Step.erase, owner.property, hraw]⟩
    | .query site owner capability arguments =>
        let _ ← AdmissionWork.length .resource arguments
        let owner ← select (RoleResolution.resolve resolver.roles owner)
        return ⟨.query site owner.val capability arguments, by simp [Step.erase, owner.property, hraw]⟩
    | .guard site owner condition =>
        let owner ← select (RoleResolution.resolve resolver.roles owner)
        return ⟨.guard site owner.val condition, by simp [Step.erase, owner.property, hraw]⟩
    | .message site wire statics sender receiver value =>
        let _ ← AdmissionWork.length .resource statics
        let sender ← select (RoleResolution.resolve resolver.roles sender)
        let receiver ← select (RoleResolution.resolve resolver.roles receiver)
        let selected ← select (resolver.wire ⟨wire, statics⟩)
        return ⟨.message site ⟨wire, statics⟩ selected.val selected.property sender.val receiver.val value,
          by simp [Step.erase, sender.property, receiver.property, hraw]⟩
    | .invoke site definition statics roles capabilities arguments =>
        let _ ← AdmissionWork.length .resource statics
        let _ ← AdmissionWork.length .resource roles
        let _ ← AdmissionWork.length .resource capabilities
        let _ ← AdmissionWork.length .resource arguments
        let selected ← select (resolver.call ⟨definition, statics, roles, capabilities⟩)
        return ⟨.invoke site ⟨definition, statics, roles, capabilities⟩ selected.val selected.property arguments,
          by simp [Step.erase, hraw]⟩
    | .repeat site count carried initial captures body =>
        let _ ← AdmissionWork.length .resource initial
        let _ ← AdmissionWork.length .resource captures
        let selected ← select (resolver.graph.count count)
        let carried ← ports resolver carried
        let body ← ProtocolResolution.body resolver (fuel - 2) body
        return ⟨.repeat site count selected.val selected.property carried.val initial captures body.val,
          by simp [Step.erase, carried.property, body.property, hraw]⟩
  termination_by sizeOf raw
  def steps (resolver : Resolver vocabulary) (fuel : Nat) (raw : List Raw.Step) :
      Admission { result : List (Step resolver) // result.map Step.erase = raw } := do
    match hraw : raw with
    | [] => return ⟨[], by simp [hraw]⟩
    | first :: rest =>
        let first ← step resolver fuel first
        let rest ← steps resolver fuel rest
        return ⟨first.val :: rest.val, by simp [first.property, rest.property, hraw]⟩
  termination_by sizeOf raw
  def body (resolver : Resolver vocabulary) : Nat → (raw : Raw.Body) →
      Admission { result : Body resolver // result.erase = raw }
    | 0, _ => throw .depth
    | fuel + 1, .mk raw terminal => do
        consume
        match terminal with
        | .ret values => let _ ← AdmissionWork.length .resource values; pure ()
        | .stop .. => pure ()
        let resolved ← steps resolver (fuel + 1) raw
        let terminal ← ProtocolResolution.terminal resolver terminal
        return ⟨.mk resolved.val terminal.val, by simp [Body.erase, resolved.property, terminal.property]⟩
  termination_by _ raw => sizeOf raw
end

structure Formed (resolver : Resolver vocabulary) (parties : List Nat)
    (capabilities : List (Protocol.Capability Nat vocabulary.Service))
    (scope : List (Protocol.Signature Nat vocabulary))
    (Γ results : List (Port Nat vocabulary.Ty)) (raw : Raw.Body) where
  participation : parties = resolver.roles.participants
  resolved : Body resolver
  erasure : resolved.erase = raw
  checked : Protocol.Formed parties vocabulary capabilities scope Γ results 0 resolved.lower

def form [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (resolver : Resolver vocabulary) (parties : List Nat)
    (capabilities : List (Protocol.Capability Nat vocabulary.Service))
    (scope : List (Protocol.Signature Nat vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra) (countValid : vocabulary.Count → Bool)
    (Γ results : List (Port Nat vocabulary.Ty)) (raw : Raw.Body)
    (signatures : Protocol.SignatureMeasurements capacity.nodes capacity.height := {}) :
    Admission (Formed resolver parties capabilities scope Γ results raw) := do
  let _ ← AdmissionWork.length .resource parties
  let roleCount ← AdmissionWork.length .resource resolver.roles.roles
  consume (roleCount * roleCount)
  if participation : parties = resolver.roles.participants then
    let resolved ← body resolver (FormationLimits.bodyDepth + 1) raw
    let checked ← (Protocol.form parties capabilities scope capacity countValid (FormationLimits.bodyDepth + 1)
      Γ results 0 resolved.val.lower signatures).mapError Error.protocol
    return ⟨participation, resolved.val, resolved.property, checked⟩
  else throw .parties

structure Admitted (resolver : Resolver vocabulary) (parties : List Nat)
    (capabilities : List (Protocol.Capability Nat vocabulary.Service))
    (scope : List (Protocol.Signature Nat vocabulary))
    (Γ results : List (Port Nat vocabulary.Ty)) (raw : Raw.Body) where
  participation : parties = resolver.roles.participants
  resolved : Body resolver
  erasure : resolved.erase = raw
  checked : Protocol.Decoded parties vocabulary capabilities scope Γ results 0 resolved.lower

def Formed.dischargeRoots {resolver parties capabilities scope Γ results raw}
    (formed : Formed (vocabulary := vocabulary) resolver parties capabilities scope Γ results raw) :
    Except Error (Admitted resolver parties capabilities scope Γ results raw) := do
  let checked ← formed.checked.dischargeRoots.mapError Error.protocol
  return ⟨formed.participation, formed.resolved, formed.erasure, checked⟩

def admit [DecidableEq vocabulary.Ty] [DecidableEq vocabulary.Service]
    (resolver : Resolver vocabulary) (parties : List Nat)
    (capabilities : List (Protocol.Capability Nat vocabulary.Service))
    (scope : List (Protocol.Signature Nat vocabulary))
    (capacity : Graph.Capacity vocabulary.toAlgebra) (countValid : vocabulary.Count → Bool)
    (Γ results : List (Port Nat vocabulary.Ty)) (raw : Raw.Body) (budget : Nat := 1000000)
    (signatures : Protocol.SignatureMeasurements capacity.nodes capacity.height := {}) :
    Except Error (Admitted resolver parties capabilities scope Γ results raw) := do
  let formed ← (form resolver parties capabilities scope capacity countValid Γ results raw signatures).run' (min budget 1000000)
  formed.dischargeRoots

end Zkc.Source.Mathematical.ProtocolResolution
