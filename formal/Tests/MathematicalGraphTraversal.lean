import Tests.MathematicalGraph
import Tests.Checks

/-! Flat graph construction must not consume one stack frame per node.
The long nested cases also exercise the recursive body's entry into the same
prefix builder. These are formation checks, not execution-cost bounds.
-/

set_option autoImplicit false
namespace Tests.MathematicalGraphTraversal
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty Op algebra publicPort)

def tuples (count : Nat) (tail : Graph.Raw Op) : Graph.Raw Op :=
  (List.range count).foldl (fun rest _ => .tuple [] rest) tail

def mixed (count : Nat) (tail : Graph.Raw Op) : Graph.Raw Op :=
  (List.range count).foldl (fun rest _ =>
    .operation .zero [] (.tuple [0] (.project 0 0
      (.map 0 [] (.outputs [0]) (.fold 0 [0] [] (.outputs [1]) rest))))) tail

def maps (count : Nat) (body : Graph.Raw Op) : Graph.Raw Op :=
  (List.range count).foldl (fun rest _ => .map 0 [] rest (.outputs [])) body

def folds (count : Nat) (body : Graph.Raw Op) : Graph.Raw Op :=
  (List.range count).foldl (fun rest _ => .fold 0 [] [] rest (.outputs [])) body

def admit (raw : Graph.Raw Op) : Except Graph.Error (List (Port Nat Ty)) :=
  (Graph.decode (algebra := algebra) [0, 1] Data.capacity MathematicalGraph.countValid 65 [] raw).map
    (·.ports)

def accepted (raw : Graph.Raw Op) (expected : List (Port Nat Ty)) : Bool :=
  match admit raw with
  | .ok actual => decide (actual = expected)
  | .error _ => false

def refused (raw : Graph.Raw Op) (error : Graph.Error) : Bool :=
  match admit raw with
  | .error actual => actual == error
  | .ok _ => false

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (accepted (tuples 20000 (.outputs [])) [])
    "20000 flat graph nodes preserve an empty result on a small stack"
  checks.holds (refused (tuples 20000 (.outputs [20000])) .scope)
    "late missing binding releases a long checked prefix and reports scope"
  checks.holds (accepted (mixed 5000 (.outputs [0])) [publicPort (.vector (.fin 0) 0)])
    "25000 mixed nodes close all five frame kinds in source order"
  checks.holds (refused (mixed 5000 (.operation .add [0, 0] (.outputs []))) .type)
    "late mixed-graph type failure keeps its diagnostic"
  checks.holds (accepted (maps 32 (tuples 20000 (.outputs []))) [])
    "long flat map body is accepted at the exact nesting boundary"
  checks.holds (accepted (folds 32 (tuples 20000 (.outputs []))) [])
    "long flat fold body is accepted at the exact nesting boundary"
  checks.holds (refused (tuples 20000 (maps 33 (.outputs []))) .depth)
    "long prefix does not reset or spend the nested map depth allowance"
  checks.holds (refused (tuples 20000 (folds 33 (.outputs []))) .depth)
    "long prefix preserves the nested fold depth refusal"
  checks.finish "mathematical graph traversal"

#eval run
end Tests.MathematicalGraphTraversal
