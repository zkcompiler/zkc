import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.Data
import Zkc.Source.Mathematical.GraphAdmission
import Zkc.Source.Mathematical.StaticNormalization

/-! One graph syntax admits an open dimension and runs under many assignments.
There is no template-only Boolean graph checker or syntax expansion by count.
-/

set_option autoImplicit false
namespace Tests.MathematicalSymbolicGraph
open Zkc.Source Zkc.Source.Mathematical

abbrev Count := Static.Expression 1
abbrev Ty := Data.Shape Unit Count
abbrev number : Ty := .atom ()
def dimension : Count := .parameter ⟨0, by decide⟩

inductive Op where
  | indexValue (count : Count)
  deriving DecidableEq, Repr

abbrev algebra : Graph.Algebra where
  Ty := Ty
  Count := Count
  Op := Op
  arguments | .indexValue count => [.fin count]
  result := fun _ => number
  index := .fin
  condition := .fin (.literal ⟨2, by decide⟩)
  Wire := fun _ => Empty
  product := .product
  vector := .vector

abbrev meaning (parameters : Fin 1 → Nat) : Graph.Interpretation algebra where
  Value := Data.Shape.Value (fun _ => Nat) (Static.Expression.eval parameters)
  count := Static.Expression.eval parameters
  pure | .indexValue _, .cons i .nil => i.val
  condition := fun value => value.val == 1
  index := id
  tuple := Data.product
  project := Data.project
  vector := id
  element := id

theorem meaning_lawful (parameters : Fin 1 → Nat) : (meaning parameters).Lawful where
  project_tuple := Data.project_product
  tuple_project := fun {types} value =>
    ⟨Data.unpack types value, Data.product_unpack types value⟩
  element_vector := fun _ _ => rfl
  vector_element := fun _ => rfl

def countValid (count : Count) : Bool := (Static.normalize count).isOk

def graph : Graph.Raw Op Count :=
  .map dimension [] (.operation (.indexValue dimension) [0] (.outputs [0])) (.outputs [0])

def admit := Graph.decode (algebra := algebra) [0] Data.capacity countValid 64 [] graph

example : admit.isOk = true := rfl
example : (admit.map fun result => result.ports) =
    .ok [⟨[0], .vector number dimension⟩] := rfl

def run (size : Nat) (index : Fin size) : Except Graph.Error Nat := do
  let checked ← admit
  let region ← checked.requirePorts [⟨[0], .vector number dimension⟩]
  return ((region.val.denote (meaning (fun _ => size)) 0 (fun v => nomatch v)).get
    .here (by simp)) index

example : run 5 3 = .ok 3 := rfl
example : run 1000000000 ⟨999999999, by decide⟩ = .ok 999999999 := rfl

-- An implicit outer reference is rejected even in symbolic mode.
example : (Graph.decode (algebra := algebra) [0] Data.capacity countValid 64 []
    (.map dimension [] (.outputs [1]) (.outputs [0]))).isOk = false := rfl

example {result} (accepted : admit = .ok result) : result.region.erase = graph :=
  Graph.decode_erases (algebra := algebra) [0] Data.capacity countValid accepted

end Tests.MathematicalSymbolicGraph
