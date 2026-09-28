import Tests.MathematicalGraph
import Tests.Checks

/-! Wide operand and deep-index regressions for intrinsic admission. These
exercise compiled rewrites as well as the ordinary Lean interpreter. They do
not establish a bound on total lookup work or sequential body construction.
-/

set_option autoImplicit false
namespace Tests.MathematicalOperandTraversal
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty number publicPort algebra)

def admit (ports : List (Port Nat Ty)) (raw : Graph.Raw MathematicalGraph.Op) :
    Except Graph.Error Unit :=
  (Graph.decode (algebra := algebra) [0, 1] Data.capacity (fun _ => true) 65 ports raw).map
    (fun _ => ())

def refused (ports : List (Port Nat Ty)) (raw : Graph.Raw MathematicalGraph.Op)
    (expected : Graph.Error) : Bool :=
  match admit ports raw with
  | .ok _ => false
  | .error actual => actual == expected

def selectedTypes (context : List Nat) (indices : List Nat) : Option (List Nat) :=
  (Graph.selectOperands context indices).toOption.map (·.ports)

def wideArgumentResult (ports : List (Port Nat Ty)) (indices : List Nat) : Except Graph.Error Unit :=
  let wideAlgebra : Graph.Algebra := { algebra with arguments := fun _ => List.replicate 65535 number }
  (Graph.decode (algebra := wideAlgebra) [0, 1] Data.capacity (fun _ => true) 65 ports
    (.operation .zero indices (.outputs [0]))).map (fun _ => ())

def hasError (result : Except Graph.Error Unit) (expected : Graph.Error) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => actual == expected

def run : IO Unit := do
  let checks ← Checks.start
  let wideProduct := publicPort (.product (List.replicate 65535 number))
  checks.holds (admit [publicPort] (.tuple (List.replicate 65535 0) (.outputs []))).isOk
    "tuple accepts the exact product node boundary on a small stack"
  checks.holds (refused [publicPort] (.tuple (List.replicate 65536 0) (.outputs [])) .resource)
    "tuple counts its root and refuses one extra operand"
  checks.holds (refused [publicPort]
    (.tuple (List.replicate 65536 0 ++ [1]) (.outputs [])) .scope)
    "invalid final operand keeps scope refusal precedence over tuple capacity"
  checks.holds (admit [wideProduct] (.project 0 65534 (.outputs []))).isOk
    "projection selects the final component of an exact-capacity product"
  checks.holds (refused [wideProduct] (.project 0 65535 (.outputs [])) .scope)
    "projection refuses the first component beyond the product"
  checks.holds (refused [wideProduct] (.project 0 18446744073709551615 (.outputs [])) .scope)
    "huge component index stops at the end of the finite context"
  checks.holds (admit (List.replicate 65535 publicPort) (.outputs [65534])).isOk
    "output selection reaches the final external binding"
  checks.holds (admit [publicPort] (.outputs (List.replicate 65535 0))).isOk
    "wide output lists preserve repeated references"
  checks.holds (refused [publicPort] (.outputs (List.replicate 65535 0 ++ [1])) .scope)
    "wide output list refuses an invalid final reference"
  checks.holds (selectedTypes [7, 11, 23] [2, 0, 2, 1] == some [23, 7, 23, 11])
    "iterative operand assembly preserves order and multiplicity"
  checks.holds (wideArgumentResult [publicPort] (List.replicate 65535 0)).isOk
    "operation admission accepts a wide typed argument list"
  checks.holds (hasError (wideArgumentResult [publicPort] (List.replicate 65534 0)) .arity)
    "wide argument selection refuses a missing final argument"
  checks.holds (hasError (wideArgumentResult [publicPort, publicPort (.fin 2)]
    (List.replicate 65534 0 ++ [1])) .type)
    "wide argument selection refuses a final type mismatch"
  checks.holds (hasError (wideArgumentResult [publicPort]
    (List.replicate 65534 0 ++ [1])) .scope)
    "wide argument selection refuses a final missing binding"
  checks.holds (hasError (wideArgumentResult [publicPort] [1]) .scope)
    "early scope refusal precedes a later argument-count mismatch"
  checks.holds (hasError (wideArgumentResult [publicPort (.fin 2)] [0]) .type)
    "early type refusal precedes a later argument-count mismatch"
  checks.holds (admit [publicPort]
    (.map 0 [0] (.outputs (List.replicate 65535 1)) (.outputs []))).isOk
    "dormant map certifies and appends a wide vector result list"
  let deepType : Ty := (List.range 64).foldl (fun type _ => .product [type]) number
  checks.holds (refused [publicPort, publicPort deepType]
    (.map 0 [0, 1] (.outputs (List.replicate 65534 1 ++ [2])) (.outputs [])) .resource)
    "wide vector result measurement refuses a late over-height result"
  let values : Values (fun _ : Nat => Nat) [0, 0, 1] := .cons 7 (.cons 9 (.cons 11 .nil))
  checks.holds ((values.map (fun n => n + 1)).toList id == [8, 10, 12])
    "iterative typed map preserves distinct values at repeated indices"
  checks.holds ((values.append values).toList id == [7, 9, 11, 7, 9, 11])
    "iterative append preserves both lists"
  let context : List (Port Nat Ty) := [⟨[2, 0], number⟩, ⟨[0], number⟩]
  match Graph.selectOperands context [0, 1, 0] with
  | .error _ => checks.holds false "availability fixture selects all operands"
  | .ok selected =>
    let inputs := Graph.toInputs (algebra := algebra) selected.values
    checks.holds (Inputs.available [2, 0, 0, 1] inputs == [0, 0])
      "iterative availability keeps participant order and multiplicity"
  checks.finish "mathematical operand traversal"

#eval run
end Tests.MathematicalOperandTraversal
