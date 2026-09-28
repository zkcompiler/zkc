import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.PortAdmission
import Zkc.Source.Mathematical.StaticResolution
import Zkc.Source.Mathematical.GraphResolution
import Tests.MathematicalTypes
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalResolvedTypes
open Zkc.Source Zkc.Source.Mathematical

abbrev Count := Static.Expression 1
abbrev Ty := TypeExpansion.Shape 0 1

def two : Count := .literal ⟨2, by decide⟩

abbrev algebra : Graph.Algebra where
  Ty := Ty
  Count := Count
  Op := Empty
  arguments := fun op => nomatch op
  result := fun op => nomatch op
  index := .fin
  condition := .fin two
  Wire := fun _ => Empty
  product := .product
  vector := .vector

def resolver : GraphResolution.Resolver algebra where
  OperationValid := fun _ _ => False
  CountValid := Static.Resolves Static.Expression.parameter
  operation := fun _ => throw "no-operations"
  count source := do
    let resolved ← fun budget => (Static.resolve Static.Expression.parameter source budget).mapError
      (fun error => toString (repr error))
    return ⟨resolved.normalized.expression, resolved.valid⟩

def templates : List Raw.TypeTemplate :=
  [⟨0, .fin (.literal 2)⟩,
   ⟨1, .vector ⟨⟨0⟩, []⟩ (.add (.parameter 0) (.literal 0))⟩]

def input : Raw.Port := ⟨[⟨0⟩], ⟨⟨0⟩, []⟩⟩
def output : Raw.Port := ⟨[⟨0⟩], ⟨⟨1⟩, [.add (.parameter 0) (.literal 0)]⟩⟩
def source : Raw.Region := .mk [⟨0⟩]
  [.map (.parameter 0) (.mk [⟨0⟩] [] [⟨1⟩])] [⟨0⟩]

def check : Except String Bool := do
  let table ← ((TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false) templates).run' 1000000).mapError (fun error => toString (repr error))
  let first ← ((PortAdmission.decode MathematicalTypes.emptyMeaning table 1 2 input).run' 1000000).mapError (fun error => toString (repr error))
  let last ← ((PortAdmission.decode MathematicalTypes.emptyMeaning table 1 2 output).run' 1000000).mapError (fun error => toString (repr error))
  let graph ← (GraphResolution.admit resolver [0, 1] Data.capacity (fun _ => true) [first.port] source).mapError (fun error => toString (repr error))
  return (graph.graph.requirePorts [last.port]).isOk

def closedInstantiation : Except TypeAdmission.Error Bool :=
  (do
    let table ← TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false) templates
    let instantiated ← TypeAdmission.instantiate MathematicalTypes.emptyMeaning table
      (fun _ : Fin 1 => (.literal ⟨8, by decide⟩ : Static.Expression 0))
      ⟨⟨1⟩, [.add (.parameter 0) (.literal 0)]⟩
    let closed ← TypeAdmission.use MathematicalTypes.emptyMeaning table 0 ⟨⟨1⟩, [.literal 8]⟩
    return decide (instantiated.expanded.shape = closed.expanded.shape)).run' 1000000

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match check with | .ok true => true | _ => false)
    "raw port and graph counts share normalized type meaning"
  checks.holds (match closedInstantiation with | .ok true => true | _ => false)
    "declaration substitution agrees with the closed type use"
  checks.holds ((PortAdmission.roles 3 0 [⟨0⟩, ⟨2⟩]).run' 100).isOk "canonical role subset"
  checks.holds (!((PortAdmission.roles 3 0 [⟨2⟩, ⟨0⟩]).run' 100).isOk) "reversed availability refused"
  checks.holds (!((PortAdmission.roles 3 0 [⟨0⟩, ⟨0⟩]).run' 100).isOk) "duplicate availability refused"
  checks.holds (!((PortAdmission.roles 3 0 [⟨3⟩]).run' 100).isOk) "role outside local scope"
  checks.holds ((PortAdmission.roles 0 0 []).run' 0).isOk "empty availability"
  checks.holds (!((Static.resolve (arity := 1) Static.Expression.parameter (.parameter 1)).run' 100).isOk)
    "static scope refused before graph lowering"
  checks.holds (!((Static.resolve (arity := 1) Static.Expression.parameter
    (.multiply (.literal 0) (.pow2 (.literal 64)))).run' 1000).isOk) "dormant static overflow"
  checks.finish "mathematical resolved type integration"

#eval run
end Tests.MathematicalResolvedTypes
