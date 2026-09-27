import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.External

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  ensure binding.arguments.isEmpty "binding-static-arguments"
  Support.realize physical binding (Support.signature shape) "native/"

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "external.monero.init" ["indices"] ["indices"] resolve,
    Operation.ofShape "external.monero.hash" ["indices"] ["indices"] resolve,
    Operation.ofShape "external.monero.update" ["indices", "indices"] ["indices", "indices"] resolve,
    Operation.ofShape "external.openvm.init" [] ["indices"] resolve,
    Operation.ofShape "external.openvm.observe" ["indices", "indices"] ["indices"] resolve,
    Operation.ofShape "external.openvm.sample" ["indices"] ["indices", "index"] resolve,
    Operation.ofShape "external.openvm.sample_ext" ["indices"] ["indices", "indices"] resolve,
    Operation.ofShape "external.openvm.sample_bits" ["indices", "index"] ["indices", "index"] resolve,
    Operation.ofShape "external.openvm.check_witness" ["indices", "index", "index"] ["indices", "bool"] resolve]⟩
  (fun contract => Support.implementations ["native"] contract)

end Tools.Interactive.Bindings.External
