import Tools.Interactive.VariantDescriptor

/-! Portable interchange syntax. This is deliberately independent of the typed
protocol language: successful raw admission is not a typed elaboration theorem. -/

set_option autoImplicit false

namespace Tools.Interactive

abbrev Result := Except String
abbrev Name := String
abbrev Ty := String

structure Limits where
  bytes : Nat := 1048576
  depth : Nat := 64
  array : Nat := 32768
  definitions : Nat := 4096
  instructions : Nat := 32768
  ports : Nat := 1024
  iterations : Nat := 1048576
  callDepth : Nat := 64
  steps : Nat := 1048576
  rank : Nat := 16
  deriving Repr

def limits : Limits := {}

def fieldModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

structure Port where
  name : Name
  owner : Name
  ty : Ty
  deriving BEq, Repr, Inhabited

inductive Count where
  | constant : Nat → Count
  | parameter : Name → Count
  deriving BEq, Repr

inductive Instruction where
  | op (site kernel : Name) (attributes inputs outputs : List String)
  | localCall (site owner function : Name) (inputs outputs : List Name)
  | message (site schema sender receiver input output : Name)
  | send (site schema peer input : Name)
  | receive (site schema peer output : Name) (ty : Ty)
  | call (site callee : Name) (inputs outputs : List Name)
  | loop (site : Name) (count : Count) (carried : List (Name × Name))
      (captures : List Name) (body : List Instruction) (outputs : List Name)
  | variant (site : Name) (ty : Ty) (alternative : Name) (payload : List Name) (output : Name)
  | localMatch (site input : Name) (captures : List Name)
      (arms : List (Name × List Name × List Instruction)) (outputs : List Name)
  | conditional (site condition : Name) (captures : List Name)
      (yes no : List Instruction) (outputs : List Name)
  | forLoop (site induction lower upper : Name) (carried : List (Name × Name))
      (captures : List Name) (body : List Instruction) (outputs : List Name)
  | yield (values : List Name)
  | release (values : List Name)
  | ret (values : List Name)
  | stop (site owner reason : Name)
  | incomplete (site : Name)
  deriving BEq, Repr

structure Function where
  name : Name
  arguments : List (Name × Ty)
  results : List Ty
  body : Option (List Instruction)
  deriving BEq, Repr

structure Dependency where
  name : Name
  protocol : Name
  agreements : List (Name × Name)
  deriving BEq, Repr

structure Protocol where
  name : Name
  roles : List Name
  parameters : List Name
  arguments : List Port
  results : List (Name × Ty)
  dependencies : List Dependency
  body : Option (List Instruction)
  deriving BEq, Repr

structure FamilySelector where
  role : Name
  function : Name
  arguments : List Name
  deriving BEq, Repr

inductive Parameter where
  | constant (value : Nat)
  | ingress (bound : Nat) (selectors : List FamilySelector)
  deriving BEq, Repr

def Parameter.bound : Parameter → Nat
  | .constant n | .ingress n _ => n

def Parameter.dynamic : Parameter → Bool
  | .constant _ => false
  | .ingress .. => true

structure Instance where
  name : Name
  protocol : Name
  parameters : List (Name × Parameter)
  dependencies : List (Name × Name)
  roles : List (Name × Name)
  deriving BEq, Repr

structure OperationBinding where
  name : String
  contract : String
  arguments : List String
  implementation : String
  deriving BEq, Repr, DecidableEq

/-- Current source always carries explicit nominal operation bindings. -/
inductive Environment where
  | explicit (bindings : List OperationBinding)
  deriving BEq, Repr

structure Source where
  environment : Environment
  functions : List Function
  protocols : List Protocol
  instances : List Instance
  entries : List (Name × Name)
  deriving BEq, Repr

structure Participant where
  name : Name
  binding : Name
  role : Name
  parameters : List (Name × Parameter)
  arguments : List (Name × Ty)
  results : List Ty
  body : List Instruction
  deriving BEq, Repr

structure Candidate where
  environment : Environment
  stage : String
  functions : List Function
  participants : List Participant
  entries : List (Name × List (Name × Name))
  deriving BEq, Repr

def ensure (condition : Bool) (code : String) : Result Unit :=
  if condition then .ok () else .error code

def lookup {α : Type} (name : Name) (bindings : List (Name × α)) : Result α :=
  match bindings.find? (fun pair => pair.1 == name) with
  | some pair => .ok pair.2
  | none => .error s!"unbound:{name}"

def unique (names : List Name) : Bool := names.eraseDups.length == names.length

def exactKeys {α β : Type} (left : List (Name × α)) (right : List (Name × β)) : Bool :=
  unique (left.map Prod.fst) && unique (right.map Prod.fst) &&
  left.length == right.length && left.all (fun x => right.any (fun y => x.1 == y.1))

def Source.function (source : Source) (name : Name) : Result Function :=
  lookup name (source.functions.map fun f => (f.name, f))

def Source.protocol (source : Source) (name : Name) : Result Protocol :=
  lookup name (source.protocols.map fun p => (p.name, p))

def Protocol.dependency (definition : Protocol) (name : Name) : Result Dependency :=
  lookup name (definition.dependencies.map fun d => (d.name, d))

def Source.binding (source : Source) (name : Name) : Result Instance :=
  lookup name (source.instances.map fun i => (i.name, i))

def Instance.role (binding : Instance) (formal : Name) : Result Name := lookup formal binding.roles

def Instance.count (binding : Instance) : Count → Result Nat
  | .constant value => .ok value
  | .parameter name => do
      match ← lookup name binding.parameters with
      | .constant n => pure n
      | .ingress .. => throw "interactive-family-unbound"

def Instance.countBound (binding : Instance) : Count → Result Nat
  | .constant n => .ok n
  | .parameter name => return (← lookup name binding.parameters).bound

def Instance.projectCount (binding : Instance) (count : Count) : Result Count := do
  match count with
  | .constant _ => pure count
  | .parameter name =>
      match ← lookup name binding.parameters with
      | .constant n => pure (.constant n)
      | .ingress .. => pure count

def typeKind (ty : Ty) : String := ((ty.splitOn "@").head!).splitOn ":" |>.head!

def serializable (ty : Ty) : Bool :=
  ["index", "indices", "matrix", "vector", "polynomial", "field", "table", "point", "round", "bool", "commitment", "commitments", "proof", "scalar", "group", "groups"].contains (typeKind ty)

/-- Checked local discard is independent of public serialization. -/
def discardable (ty : Ty) : Bool :=
  Variant.allLeaves (fun ty => typeKind ty == "resource_unit" || serializable ty || ["opening_state", "opening_states", "prover_key", "verifier_key"].contains (typeKind ty)) 8 ty

/-- Positive local aliasing permission; unknown abstract types do not gain it
merely by lacking an affine annotation. -/
def duplicable (ty : Ty) : Bool :=
  Variant.allLeaves (fun ty => serializable ty || ["opening_state", "opening_states", "prover_key", "verifier_key"].contains (typeKind ty)) 8 ty

def affine (ty : Ty) : Bool :=
  (typeKind ty == "variant" && !duplicable ty) || ["resource_unit", "rng", "nonce", "transcript"].contains (typeKind ty) || ty.startsWith "capability:"


def abstractType (ty : Ty) : Bool := ty.startsWith "opaque:" || ty.startsWith "capability:"

end Tools.Interactive
