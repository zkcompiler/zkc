import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Native

private def provider (contract : String) : String :=
  if contract.startsWith "index." || contract.startsWith "indices." then "native" else "arkworks"

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  ensure binding.arguments.isEmpty "binding-static-arguments"
  -- Boolean/control implementations retain their historical arkworks identity.
  let backend := provider binding.contract ++ "/"
  Support.realize physical binding (Support.signature shape) backend

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "index.constant" [] ["index"] resolve,
    Operation.ofShape "index.add" ["index", "index"] ["index"] resolve,
    Operation.ofShape "index.sub" ["index", "index"] ["index"] resolve,
    Operation.ofShape "index.mul" ["index", "index"] ["index"] resolve,
    Operation.ofShape "index.div" ["index", "index"] ["index"] resolve,
    Operation.ofShape "index.mod" ["index", "index"] ["index"] resolve,
    Operation.ofShape "index.equal" ["index", "index"] ["bool"] resolve,
    Operation.ofShape "index.less" ["index", "index"] ["bool"] resolve,
    Operation.ofShape "indices.empty" [] ["indices"] resolve,
    Operation.ofShape "indices.append" ["indices", "index"] ["indices"] resolve,
    Operation.ofShape "indices.at" ["indices", "index"] ["index"] resolve,
    Operation.ofShape "indices.length" ["indices"] ["index"] resolve,
    Operation.ofShape "bool.and" ["bool", "bool"] ["bool"] resolve,
    Operation.ofShape "bool.or" ["bool", "bool"] ["bool"] resolve,
    Operation.ofShape "bool.not" ["bool"] ["bool"] resolve,
    Operation.ofShape "control.require" ["bool"] [] resolve]⟩
  (fun contract => Support.implementations [provider contract] contract)

end Tools.Interactive.Bindings.Native
