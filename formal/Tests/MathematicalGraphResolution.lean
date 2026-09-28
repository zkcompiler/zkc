import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.GraphResolution
import Tests.MathematicalGraph
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalGraphResolution
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty Op algebra number publicPort meaning countValid)

inductive Installed : GraphResolution.OperationUse → Op → Prop where
  | zero : Installed ⟨⟨0⟩, [], .object []⟩ .zero
  | add : Installed ⟨⟨1⟩, [], .object []⟩ .add
  | index (count : Nat) : Installed ⟨⟨2⟩, [.literal count], .object []⟩ (.indexValue count)

def resolver : GraphResolution.Resolver algebra where
  OperationValid := Installed
  CountValid source count := source = .literal count ∧ count < Static.limit
  operation source := match source with
    | ⟨⟨0⟩, [], .object []⟩ => return ⟨.zero, .zero⟩
    | ⟨⟨1⟩, [], .object []⟩ => return ⟨.add, .add⟩
    | ⟨⟨2⟩, [.literal count], .object []⟩ => return ⟨.indexValue count, .index count⟩
    | _ => throw "uninstalled-operation"
  count source := match source with
    | .literal count =>
        if h : count < Static.limit then return ⟨count, rfl, h⟩ else throw "count-overflow"
    | _ => throw "not-a-literal"

def admit (Γ : List (Port Nat Ty)) (raw : Raw.Region) (budget : Nat := 1000000) :=
  GraphResolution.admit resolver [0, 1] Data.capacity countValid Γ raw budget

def indexMap (count : Nat) : Raw.Region :=
  .mk [] [.map (.literal count)
    (.mk [] [.operation ⟨2⟩ [.literal count] (.object []) [⟨0⟩]] [⟨0⟩])] [⟨0⟩]

def runMap (count : Nat) (index : Fin count) : Except GraphResolution.Error Nat := do
  let result ← admit [] (indexMap count)
  let graph ← (result.graph.requirePorts [publicPort (.vector number count)]).mapError GraphResolution.Error.graph
  -- The admitted capture selection supplies the actual graph environment.
  let empty : Environment meaning.Value 0 [] := fun v => nomatch v
  let captured := Operands.eval empty result.captured.values
  let values := graph.val.denote meaning 0 (fun v => captured.get v)
  return values.get .here (by simp) index

example {Γ raw} (result : GraphResolution.Admitted resolver [0, 1] Γ raw) :
    result.resolved.erase = raw := result.erasure

example {Γ raw} (result : GraphResolution.Admitted resolver [0, 1] Γ raw) :
    result.graph.region.erase = result.resolved.lower := result.graph.erasure

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match runMap 5 3 with | .ok 3 => true | _ => false) "carrier map reaches typed execution"
  checks.holds (admit [] (indexMap 1000000000)).isOk "large count remains compact"
  checks.holds (!(admit [] (.mk [] [.operation ⟨99⟩ [] (.object []) []] [])).isOk)
    "unknown operation"
  checks.holds (!(admit [] (.mk [] [.operation ⟨0⟩ [] (.object [("forged", .boolean true)]) []] [])).isOk)
    "authored attributes require installed selection"
  checks.holds (!(admit [publicPort] (.mk [] [.map (.literal 0) (.mk [] [] [⟨1⟩])] [])).isOk)
    "dormant implicit capture"
  checks.holds (!(admit [] (.mk [⟨0⟩] [] [])).isOk) "outer capture reference"
  checks.holds (!(admit [] (indexMap 3) 0).isOk) "shared resolution budget"
  let replenishing : GraphResolution.Resolver algebra := { resolver with count := fun source => do
    modify (· + 1)
    resolver.count source }
  checks.holds (match GraphResolution.admit replenishing [0, 1] Data.capacity
    countValid [] (indexMap 3) with
    | .error .resource => true | _ => false)
    "installed count resolver cannot replenish the caller's allowance"
  checks.finish "mathematical carrier graph resolution"

#eval run
end Tests.MathematicalGraphResolution
