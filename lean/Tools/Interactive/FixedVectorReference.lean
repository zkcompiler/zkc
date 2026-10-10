import Tools.Interactive.ScalarReference

/-! Independent numerical meaning of the installed KoalaBear fixed-vector
witness. The carrier retains its element identity, natural index and an exact
length proof. No transcript codec or cryptographic primitive is introduced. -/

set_option autoImplicit false
namespace Tools.Interactive.FixedVectorReference

abbrev Scalar := ScalarReference.Scalar .koalaBear

structure Data where
  element : Logical.GroundType
  length : Nat
  values : List Scalar
  exactLength : values.length = length

def Data.ty (value : Data) : Bindings.ValueType :=
  Bindings.ValueType.ofLogical (.application "fixed_vector" [.type value.element, .natural value.length])

def Data.validate (value : Data) : Result Unit := do
  ensure (value.length ≤ Logical.naturalLimit) "binding-type-natural"
  ensure (value.element == .atom "field" Bindings.koalaBear) "reference-fixed-vector-not-supported"

def admit (element : Logical.GroundType) (length : Nat) (values : List Scalar) : Result Data := do
  ensure (length ≤ Logical.naturalLimit) "binding-type-natural"
  ensure (element == .atom "field" Bindings.koalaBear) "reference-fixed-vector-not-supported"
  if exactLength : values.length = length then return ⟨element, length, values, exactLength⟩
  else throw "fixed-vector-length"

/-- Both arguments retain their nominal index. Zip cannot silently truncate:
the two length proofs and the identity check precede numerical evaluation. -/
def dot (left right : Data) : Result Scalar := do
  left.validate
  right.validate
  ensure (left.element == right.element && left.length == right.length) "reference-value-type"
  return ((left.values.zip right.values).map fun (x, y) => x * y).sum

theorem length_invariant (value : Data) : value.values.length = value.length := value.exactLength

end Tools.Interactive.FixedVectorReference
