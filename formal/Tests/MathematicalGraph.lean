import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.Data
import Zkc.Source.Mathematical.GraphAdmission

set_option autoImplicit false
namespace Tests.MathematicalGraph
open Zkc.Source Zkc.Source.Mathematical

abbrev Ty := Data.Shape Unit
abbrev number : Ty := .atom ()

inductive Op where
  | zero
  | add
  | appendIndex (count : Nat)
  | indexValue (count : Nat)
  deriving DecidableEq, Repr

abbrev algebra : Graph.Algebra where
  Ty := Ty
  Op := Op
  arguments
    | .zero => []
    | .add => [number, number]
    | .appendIndex count => [number, .fin count]
    | .indexValue count => [.fin count]
  result := fun _ => number
  index := .fin
  condition := .fin 2
  Wire := fun _ => Empty
  product := .product
  vector := .vector

abbrev meaning : Graph.Interpretation algebra where
  Value := Data.Shape.Value (fun _ => Nat) id
  count := id
  pure
    | .zero, .nil => 0
    | .add, .cons a (.cons b .nil) => a + b
    | .appendIndex _, .cons a (.cons b .nil) => 10 * a + b.val
    | .indexValue _, .cons i .nil => i.val
  condition := fun value => value.val == 1
  index := id
  tuple := Data.product
  project := Data.project
  vector := id
  element := id

theorem meaning_lawful : meaning.Lawful where
  project_tuple := Data.project_product
  tuple_project := fun {types} value =>
    ⟨Data.unpack types value, Data.product_unpack types value⟩
  element_vector := fun _ _ => rfl
  vector_element := fun _ => rfl

abbrev publicPort (ty : Ty := number) : Port Nat Ty := ⟨[0, 1], ty⟩
abbrev privatePort (ty : Ty := number) : Port Nat Ty := ⟨[0], ty⟩

def countValid (n : Nat) : Bool := n < Static.limit

def admit (Γ : List (Port Nat Ty)) (raw : Graph.Raw Op) :=
  Graph.decode (algebra := algebra) [0, 1] Data.capacity countValid 64 Γ raw

def outputPorts (Γ : List (Port Nat Ty)) (raw : Graph.Raw Op) :
    Except Graph.Error (List (Port Nat Ty)) := return (← admit Γ raw).ports

def runNumber (Γ : List (Port Nat Ty)) (raw : Graph.Raw Op)
    (env : Environment meaning.Value 0 Γ) : Except Graph.Error Nat := do
  let graph ← admit Γ raw
  let region ← graph.requirePorts [publicPort number]
  return ((region.val.denote meaning 0 env).get .here) (by decide)

def tupleProjection : Graph.Raw Op := .tuple [0, 1] (.project 0 1 (.outputs [0]))

example : outputPorts [publicPort, publicPort] tupleProjection = .ok [publicPort] := by rfl

example : runNumber [publicPort, publicPort] tupleProjection
    (fun v => match v with | .here => fun _ => 7 | .there .here => fun _ => 19) = .ok 19 := by rfl

-- The whole product's availability survives projection, even if its selected
-- element was public before packing it with a private element.
example : outputPorts [publicPort, privatePort] tupleProjection = .ok [privatePort] := by rfl

def foldDigits (count : Nat) : Graph.Raw Op :=
  .fold count [0] []
    (.operation (.appendIndex count) [1, 0] (.outputs [0])) (.outputs [0])

example : runNumber [publicPort] (foldDigits 3)
    (fun v => match v with | .here => fun _ => 0) = .ok 12 := by rfl

example : runNumber [publicPort] (foldDigits 0)
    (fun v => match v with | .here => fun _ => 9) = .ok 9 := by rfl

def indexMap (count : Nat) : Graph.Raw Op :=
  .map count [] (.operation (.indexValue count) [0] (.outputs [0])) (.outputs [0])

def runMap (count : Nat) (index : Fin count) : Except Graph.Error Nat := do
  let graph ← admit [] (indexMap count)
  let region ← graph.requirePorts [publicPort (.vector number count)]
  let values := region.val.denote meaning 0 (fun v => nomatch v)
  return values.get .here (by simp) index

example : runMap 5 3 = .ok 3 := by rfl

-- Admission never evaluates or unrolls this count.
example : outputPorts [] (indexMap 1000000000) =
    .ok [publicPort (.vector number 1000000000)] := by rfl

example : outputPorts [] (.map 0 [] (.outputs [1]) (.outputs [0])) = .error .scope := by rfl

-- A zero-count fold still checks its body and its exact invariant.
example : outputPorts [publicPort] (.fold 0 [0] [] (.outputs [0]) (.outputs [0])) =
    .error .invariant := by rfl

-- No implicit read through a capture list that omits the outer operand.
example : outputPorts [publicPort] (.map 2 [] (.outputs [1]) (.outputs [0])) = .error .scope := by rfl

-- A captured but unused private component does not taint a nullary public node.
example : outputPorts [privatePort]
    (.map 2 [0] (.operation .zero [] (.outputs [0])) (.outputs [0])) =
    .ok [publicPort (.vector number 2)] := by rfl

-- Exact fold availability rejects widening as well as narrowing.
example : outputPorts [privatePort]
    (.fold 0 [0] [] (.operation .zero [] (.outputs [0])) (.outputs [0])) =
    .error .invariant := by rfl

example : outputPorts [publicPort] (.operation .add [0] (.outputs [0])) = .error .arity := by rfl
example : outputPorts [publicPort (.fin 2), publicPort]
    (.operation .add [0, 1] (.outputs [0])) = .error .type := by rfl
example : outputPorts [publicPort] (.project 0 0 (.outputs [0])) = .error .product := by rfl
example : outputPorts [publicPort (.vector number 3)] (.project 0 0 (.outputs [0])) =
    .error .product := by rfl
example : outputPorts [publicPort (.product [number])] (.project 0 1 (.outputs [0])) =
    .error .scope := by rfl
example : outputPorts [publicPort] (.outputs [0, 0]) = .ok [publicPort, publicPort] := by rfl
example : outputPorts [] (.tuple [] (.outputs [0])) = .ok [publicPort (.product [])] := by rfl

-- An empty availability intersection is a typed value with no role component.
example : outputPorts [⟨[0], number⟩, ⟨[1], number⟩]
    (.operation .add [0, 1] (.outputs [0])) = .ok [⟨[], number⟩] := by rfl

example : (Graph.decode (algebra := algebra) [0, 1] Data.capacity countValid 0 []
    (.outputs [])).isOk = false := by rfl

-- The erasure equation is carried by every successful output, including a
-- structured graph with projection or an indexed body.
example {raw : Graph.Raw Op} {Γ result} (h : admit Γ raw = .ok result) :
    result.region.erase = raw :=
  Graph.decode_erases (algebra := algebra) [0, 1] Data.capacity countValid (fuel := 64) h

end Tests.MathematicalGraph
