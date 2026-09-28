import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.ProtocolResolution
import Tests.MathematicalGraphResolution
import Tests.MathematicalProtocolMeaning
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalProtocolResolution
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (number publicPort privatePort)
open MathematicalProtocol (vocabulary capabilities Local)
open MathematicalProtocolMeaning (meaning execute Event)

inductive InstalledLocal : GraphResolution.OperationUse → Local → Prop where
  | shared : InstalledLocal ⟨⟨3⟩, [], .object []⟩ .shared
  | distinct : InstalledLocal ⟨⟨4⟩, [], .object []⟩ .distinct

inductive InstalledWire : ProtocolResolution.WireUse → ((ty : vocabulary.Ty) × vocabulary.Wire ty) → Prop where
  | number : InstalledWire ⟨⟨0⟩, []⟩ ⟨number, ()⟩

inductive InstalledPort : Raw.Port → Port Nat vocabulary.Ty → Prop where
  | privateNumber : InstalledPort ⟨[⟨0⟩], ⟨⟨0⟩, []⟩⟩ privatePort

def resolver : ProtocolResolution.Resolver vocabulary where
  roles := ⟨[0, 1], by decide⟩
  graph := {
    OperationValid := MathematicalGraphResolution.resolver.OperationValid
    CountValid := MathematicalGraphResolution.resolver.CountValid
    operation := MathematicalGraphResolution.resolver.operation
    count := MathematicalGraphResolution.resolver.count }
  LocalValid := InstalledLocal
  WireValid := InstalledWire
  CallValid := fun _ _ => False
  PortValid := InstalledPort
  localOperation source := match source with
    | ⟨⟨3⟩, [], .object []⟩ => return ⟨.shared, .shared⟩
    | ⟨⟨4⟩, [], .object []⟩ => return ⟨.distinct, .distinct⟩
    | _ => throw "uninstalled-local"
  wire source := match source with
    | ⟨⟨0⟩, []⟩ => return ⟨⟨number, ()⟩, .number⟩
    | _ => throw "uninstalled-wire"
  call _ := throw "no-stored-definition"
  port source := match source with
    | ⟨[⟨0⟩], ⟨⟨0⟩, []⟩⟩ => return ⟨privatePort, .privateNumber⟩
    | _ => throw "uninstalled-port"

def admit (raw : Raw.Body) := ProtocolResolution.admit resolver [0, 1] capabilities []
  Data.capacity MathematicalGraph.countValid [privatePort] [publicPort] raw

def shared : Raw.Body := .mk
  [.query 0 ⟨0⟩ ⟨0⟩ [⟨0⟩], .query 1 ⟨0⟩ ⟨1⟩ [⟨0⟩],
   .message 2 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])

def repeated (count : Nat) : Raw.Body := .mk
  [.repeat 0 (.literal count) [⟨[⟨0⟩], ⟨⟨0⟩, []⟩⟩] [⟨0⟩] []
    (.mk [.query 1 ⟨0⟩ ⟨0⟩ [⟨1⟩]] (.ret [⟨0⟩])),
   .message 2 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])

def runBody (raw : Raw.Body) : Except String (Nat × Nat × List Event) := do
  let result ← (admit raw).mapError (fun _ => "admission")
  let inputs : Values (Component meaning.Value 0) [privatePort] := .cons (fun _ => 9) .nil
  let process := result.checked.program.openMeaning meaning 0 (fun v => inputs.get v)
  let (values, state, trace) ← execute 32 process (fun _ => 0)
  return (values.get .here (by decide), state 7, trace)

example {raw} (result : ProtocolResolution.Admitted resolver [0, 1] capabilities []
    [privatePort] [publicPort] raw) : result.resolved.erase = raw := result.erasure

example {raw} (result : ProtocolResolution.Admitted resolver [0, 1] capabilities []
    [privatePort] [publicPort] raw) : result.checked.program.erase = result.resolved.lower := result.checked.erasure

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match runBody shared with
    | .ok (1, 2, [⟨⟨[], 0⟩, some 7⟩, ⟨⟨[], 1⟩, some 7⟩, ⟨⟨[], 2⟩, none⟩]) => true
    | _ => false) "carrier aliases reach the same root state"
  checks.holds (match runBody (repeated 3) with
    | .ok (2, 3, [⟨⟨[.iteration 0 0], 1⟩, some 7⟩, ⟨⟨[.iteration 0 1], 1⟩, some 7⟩,
        ⟨⟨[.iteration 0 2], 1⟩, some 7⟩, ⟨⟨[], 2⟩, none⟩]) => true
    | _ => false) "carrier repeat preserves sites and state"
  checks.holds (match runBody (repeated 0) with
    | .ok (9, 0, [⟨⟨[], 2⟩, none⟩]) => true | _ => false) "zero repeat checks dormant site layout"
  checks.holds (admit (repeated 1000000000)).isOk "large repeat remains compact"
  checks.holds (!(admit (.mk [.message 1 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩]))).isOk)
    "carrier site order"
  checks.holds (!(admit (.mk [.local 0 ⟨0⟩ ⟨4⟩ [] (.object []) [⟨0⟩, ⟨1⟩] [⟨0⟩]] (.ret [⟨0⟩]))).isOk)
    "registered distinctness checks actual aliases"
  checks.holds (!(admit (.mk [.invoke 0 ⟨0⟩ [] [⟨0⟩] [] []] (.ret []))).isOk)
    "stored call requires a declaration witness"
  let swapped := { resolver with roles := ⟨[1, 0], by decide⟩ }
  checks.holds (ProtocolResolution.admit swapped [0, 1] capabilities [] Data.capacity
    MathematicalGraph.countValid [⟨[1], number⟩] [publicPort]
    (.mk [.message 0 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩]))).isOk
    "non-monotone role binding retains canonical message availability"
  checks.holds (!(ProtocolResolution.admit swapped [0, 1, 2] capabilities [] Data.capacity
    MathematicalGraph.countValid [] [] (.mk [] (.ret []))).isOk)
    "unbound participant cannot be added"
  checks.holds (!(admit (.mk [] (.stop 0 ⟨2⟩ .reject))).isOk) "terminal owner must resolve in the role binding"
  let replenishing : ProtocolResolution.Resolver vocabulary := { resolver with wire := fun source => do
    modify (· + 1)
    resolver.wire source }
  checks.holds (match ProtocolResolution.admit replenishing [0, 1] capabilities []
    Data.capacity MathematicalGraph.countValid [privatePort] [publicPort]
    (.mk [.message 0 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩] (.ret [⟨0⟩])) with
    | .error .resource => true | _ => false)
    "installed wire resolver cannot replenish the caller's allowance"
  checks.finish "mathematical carrier protocol resolution"

#eval run
end Tests.MathematicalProtocolResolution
