import Tools.Interactive.Bindings.Types

set_option autoImplicit false

namespace Tools.Interactive.Bindings

/-- An independently authored operation, with its generic shape when exposed by
that API. Resolution checks complete logical and selected physical bindings. -/
structure Operation where
  contract : String
  shape : Option (List String × List String)
  resolve : Bool → Declaration → Result Signature
  implementations : List String := []

/-- Keep a shape and its full-type resolver together without a second name table. -/
def Operation.ofShape (contract : String) (inputs outputs : List String)
    (resolve : Bool → Declaration → (List String × List String) → Result Signature) : Operation :=
  ⟨contract, some (inputs, outputs), fun physical binding => resolve physical binding (inputs, outputs), []⟩

/-- A domain owns a finite set of exact contract names and their interpretations. -/
structure Contribution where
  operations : List Operation

/-- Domain-owned implementation names are discovery and partial-selection data.
The full resolver must still establish nominal applicability. -/
def Contribution.withImplementations (contribution : Contribution)
    (names : String → List String) : Contribution :=
  ⟨contribution.operations.map fun operation =>
    { operation with implementations := names operation.contract }⟩

/-- An explicitly assembled, immutable installation; registration order never
selects between competing meanings of a contract. No execution support is implied. -/
structure Installation where
  operations : Std.HashMap String Operation

/-- Reject duplicate ownership before any binding is resolved. -/
def assemble (contributions : List Contribution) : Result Installation := do
  let mut operations : Std.HashMap String Operation := {}
  for contribution in contributions do
    for operation in contribution.operations do
      ensure (!operations.contains operation.contract) "binding-duplicate-contract"
      ensure (operation.implementations.all (!·.isEmpty) &&
        operation.implementations.eraseDups.length == operation.implementations.length)
        "binding-implementation-registration"
      operations := operations.insert operation.contract operation
  return ⟨operations⟩

def Installation.operation (installation : Installation) (contract : String) : Result Operation :=
  match installation.operations[contract]? with
  | some operation => .ok operation
  | none => .error "binding-contract"

def Installation.shape (installation : Installation) (contract : String) : Result (List String × List String) := do
  let operation ← installation.operation contract
  match operation.shape with
  | some shape => return shape
  | none => throw "binding-contract"

def Installation.resolve (installation : Installation) (physical : Bool)
    (binding : Declaration) : Result Signature := do
  let operation ← installation.operation binding.contract
  let signature ← operation.resolve physical binding
  -- Preserve domain-specific refusal precedence. Even a permissive resolver
  -- cannot admit a physical identity absent from its independent registration.
  ensure ((!physical && binding.implementation.isEmpty) ||
    operation.implementations.contains binding.implementation) "binding-implementation"
  return signature

/-- Registered names, not a claim that every nominal instantiation is supported. -/
def Installation.implementations (installation : Installation) : List (String × String) :=
  installation.operations.toList.flatMap fun (contract, operation) =>
    operation.implementations.map (contract, ·)

end Tools.Interactive.Bindings
