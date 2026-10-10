import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Matrix

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let field ← Support.scalarArgument binding
  Support.realize physical binding (Support.signature shape field) (Support.scalarBackend field)

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "matrix.mul_vector" ["matrix", "vector"] ["vector"] resolve,
    Operation.ofShape "matrix.transpose_mul_vector" ["matrix", "vector"] ["vector"] resolve,
    Operation.ofShape "matrix.bilinear" ["matrix", "vector", "vector"] ["field"] resolve,
    Operation.ofShape "matrix.identity_check" ["matrix"] ["bool"] resolve,
    Operation.ofShape "matrix.shape_check" ["matrix"] ["bool"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract)

end Tools.Interactive.Bindings.Matrix
