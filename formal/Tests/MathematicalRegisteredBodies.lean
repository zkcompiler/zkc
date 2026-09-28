import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.RegisteredVocabulary
import Tests.MathematicalDeclarations

set_option autoImplicit false
namespace Tests.MathematicalRegisteredBodies
open Zkc.Source.Mathematical
open MathematicalDeclarations (subject contracts)

def roles : RoleResolution.Binding := ⟨[0, 1], by decide⟩
def parameters : Fin 1 → Static.Expression 0 := fun _ => .literal ⟨3, by decide⟩
def noCalls : RegisteredVocabulary.Calls := ⟨fun _ _ => False, fun _ => throw "no-calls"⟩

def boolean : Raw.Port := ⟨[⟨0⟩], MathematicalDeclarations.booleanUse⟩
def vector : Raw.Port := ⟨[⟨0⟩], ⟨⟨1⟩, [.parameter 0]⟩⟩
def received : Raw.Port := ⟨[⟨0⟩, ⟨1⟩], vector.type⟩

private def asString {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

def check (raw : Raw.Body) (input output : Raw.Port) (binding : RoleResolution.Binding := roles) : Except String Bool :=
  (show StateT Nat (Except String) Bool from do
    let header ← asString (DeclarationAdmission.admit contracts subject)
    let argument ← asString (PortAdmission.instantiate header.context.meaning header.types parameters binding input)
    let result ← asString (PortAdmission.instantiate header.context.meaning header.types parameters binding output)
    let root := header.roots.get .here
    let capabilities := [Protocol.Capability.mk ⟨root.signature.service, root.roles.values⟩ 0]
    let resolver := RegisteredVocabulary.protocol header parameters binding noCalls
    let checked ← (ProtocolResolution.admit resolver binding.participants capabilities [] Data.capacity (fun _ => true)
      [argument.port] [result.port] raw 1000000 (RegisteredVocabulary.signatureMeasurements header 0)).mapError
      (fun error => toString (repr error))
    return checked.checked.program.sites == List.range checked.checked.finish).run' 1000000

def copied : Raw.Body := .mk
  [.pure (.mk [⟨0⟩] [.operation ⟨0⟩ [] (.object []) [⟨0⟩]] [⟨0⟩])] (.ret [⟨0⟩])

def gated : Raw.Body := .mk [.local 0 ⟨0⟩ ⟨1⟩ [.parameter 0] (.object []) [⟨0⟩] [⟨0⟩]] (.ret [⟨0⟩])

def message : Raw.Body := .mk [.message 0 ⟨0⟩ [.parameter 0] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])

def query : Raw.Body := .mk [.query 0 ⟨0⟩ ⟨0⟩ [⟨0⟩]] (.ret [⟨0⟩])

/-- Disable every generic boundary walk after the context is certified. Each
operation, local step, query and wire must use the retained root counters. -/
def cachedCheck (raw : Raw.Body) (input output : Raw.Port) (known : Bool) : Except String (Except Protocol.Error Unit) :=
  (show StateT Nat (Except String) (Except Protocol.Error Unit) from do
    let header ← asString (DeclarationAdmission.admit contracts subject)
    let argument ← asString (PortAdmission.instantiate header.context.meaning header.types parameters roles input)
    let result ← asString (PortAdmission.instantiate header.context.meaning header.types parameters roles output)
    let resolver := RegisteredVocabulary.protocol header parameters roles noCalls
    let resolved ← asString (ProtocolResolution.body resolver 65 raw)
    let capacity : Graph.Capacity (RegisteredVocabulary.vocabulary header 0).toAlgebra :=
      { Data.capacity with measure := fun _ => none }
    let signatures := RegisteredVocabulary.signatureMeasurements header 0
    let formed := Protocol.formMeasured roles.participants header.capabilities [] capacity (fun _ => true)
      65 [argument.port] [result.port] (.cons argument.type.expanded.measured .nil)
      (.cons result.type.expanded.measured .nil) 0 resolved.val.lower
      (if known then signatures else {})
    return formed.map (fun _ => ())).run' 1000000

/-- An empty external context isolates forwarding through both resolution and
intrinsic formation. The installed test operation has no arguments. -/
def cachedResolution (known : Bool) : Except String (Except ProtocolResolution.Error Unit) :=
  (show StateT Nat (Except String) (Except ProtocolResolution.Error Unit) from do
    let source := { subject with module.operations :=
      subject.module.operations.modify 0 (fun op => { op with arguments := [] }) }
    let registry := { contracts with
      operation := fun manifest code signature =>
        if signature = ⟨MathematicalDeclarations.copy, [], [], [], MathematicalDeclarations.boolean⟩ then
          some ⟨.total, []⟩
        else contracts.operation manifest code signature }
    let header ← asString (DeclarationAdmission.admit registry source)
    let resolver := RegisteredVocabulary.protocol header parameters roles noCalls
    let capacity : Graph.Capacity (RegisteredVocabulary.vocabulary header 0).toAlgebra :=
      { Data.capacity with measure := fun _ => none }
    let signatures := RegisteredVocabulary.signatureMeasurements header 0
    let body : Raw.Body := .mk [.pure ⟨[], [.operation ⟨0⟩ [] (.object []) []], []⟩] (.ret [])
    return (ProtocolResolution.admit resolver roles.participants header.capabilities [] capacity (fun _ => true)
      [] [] body 1000000 (if known then signatures else {})).map (fun _ => ())).run' 1000000

def repeated (count : Nat) (body : Raw.Body := .mk [] (.ret [⟨1⟩])) : Raw.Body := .mk
  [.repeat 0 (.literal count) [vector] [⟨0⟩] [] body,
    .message 1 ⟨0⟩ [.parameter 0] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])

def accepts (body : Raw.Body) (input output : Raw.Port) (binding : RoleResolution.Binding := roles) : Bool :=
  match check body input output binding with
  | .ok result => result
  | .error _ => false

-- An operation in a resolved region retains a real signature instantiated
-- under this resolver's parameters, not just the requested operation number.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {arity target} (parameters : Fin arity → Static.Expression target)
    {raw operation} (valid : (RegisteredVocabulary.graph header parameters).OperationValid raw operation) :
    RegisteredVocabulary.OperationResolves header parameters raw operation.val := valid

def run : IO Unit := do
  let checks ← Checks.start
  for (body, input, output, label, expected) in
      [(copied, boolean, boolean, "pure operation", Protocol.Error.graph .resource),
        (gated, vector, boolean, "local operation", .resource),
        (query, vector, boolean, "service query", .resource),
        (message, vector, received, "wire payload", .resource)] do
    checks.holds (match cachedCheck body input output true with | .ok (.ok ()) => true | _ => false)
      s!"{label} reuses admitted signature measurements with boundary walks disabled"
    checks.holds (match cachedCheck body input output false with | .ok (.error error) => error == expected | _ => false)
      s!"{label} control needs a boundary walk when retained measurements are absent"
  checks.holds (match cachedResolution true with | .ok (.ok ()) => true | _ => false)
    "carrier resolution forwards retained measurements through full body admission"
  checks.holds (match cachedResolution false with | .ok (.error (.protocol (.graph .resource))) => true | _ => false)
    "carrier resolution control refuses at the missing operation measurement"
  checks.holds (accepts copied boolean boolean) "raw pure node selects actual registered total operation"
  checks.holds (accepts gated vector boolean) "raw local resolves static-dependent capability signature"
  checks.holds (accepts message vector received) "raw wire resolves the actual payload type"
  checks.holds (accepts message vector received ⟨[1, 0], by decide⟩) "registered wire under a non-monotone role map"
  checks.holds (accepts (repeated 1000000000) vector received) "registered port and count in compact large repeat"
  checks.holds (accepts (.mk [.query 0 ⟨0⟩ ⟨0⟩ [⟨0⟩], .query 1 ⟨0⟩ ⟨0⟩ [⟨1⟩]] (.ret [⟨0⟩])) vector boolean)
    "queries select the admitted root service"
  checks.holds (accepts (.mk [.guard 0 ⟨0⟩ ⟨0⟩] (.ret [⟨0⟩])) boolean boolean)
    "condition type is the same normalized Fin2 as the admitted port"
  checks.holds (!(accepts copied vector boolean)) "operation operands must have the registered type"
  checks.holds (!(accepts (.mk
    [.pure (.mk [⟨0⟩] [.operation ⟨1⟩ [.parameter 0] (.object []) [⟨0⟩]] [⟨0⟩])] (.ret [⟨0⟩])) vector boolean))
    "ordered registry operation cannot enter a pure region"
  checks.holds (!(accepts (.mk [.local 0 ⟨0⟩ ⟨0⟩ [] (.object []) [] [⟨0⟩]] (.ret [⟨0⟩])) boolean boolean))
    "total operation is not an ordered local"
  checks.holds (!(accepts (.mk
    [.local 0 ⟨0⟩ ⟨2⟩ [.parameter 0] (.object []) [⟨0⟩, ⟨0⟩] [⟨0⟩]] (.ret [⟨0⟩])) vector boolean))
    "registered distinctness checks actual root aliases"
  checks.holds (!(accepts (.mk [.local 0 ⟨0⟩ ⟨1⟩ [.literal 4] (.object []) [⟨0⟩] [⟨0⟩]] (.ret [⟨0⟩])) vector boolean))
    "operation cannot substitute another service dimension"
  checks.holds (!(accepts (.mk [.message 0 ⟨0⟩ [.literal 4] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])) vector received))
    "wire static mismatch"
  checks.holds (!(accepts (.mk
    [.pure (.mk [⟨0⟩] [.operation ⟨0⟩ [] (.object [("forged", .boolean true)]) [⟨0⟩]] [⟨0⟩])] (.ret [⟨0⟩])) boolean boolean))
    "actual operation use checks its registered attribute schema"
  checks.holds (!(accepts (repeated 0 (.mk
    [.pure (.mk [⟨1⟩] [.operation ⟨0⟩ [] (.object []) [⟨0⟩]] [⟨0⟩])] (.ret [⟨1⟩]))) vector received))
    "zero repeat cannot hide an ill-typed registered operation"
  checks.holds (!(accepts (.mk [.invoke 0 ⟨0⟩ [] [] [] []] (.ret [⟨0⟩])) boolean boolean))
    "unresolved stored call cannot borrow operation authority"
  checks.finish "mathematical registered body integration"

#eval run
end Tests.MathematicalRegisteredBodies
