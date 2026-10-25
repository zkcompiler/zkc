module

public import Zkc.Construction.Participant

@[expose] public section

/-! The executable validator stage of a native proof deployment.

The bridge reads the validator participant that a `zkc.program/0` artifact
selects for the deployment's entry and validator role, together with the local
functions and operation bindings it reaches, into this carrier. It keeps the
artifact's names, sites, physical types and binding records. Occurrence
templates in operation parameters are decoded and re-encoded exactly by the
bridge; every other parameter is kept as text. Participant bodies keep their
value-counted loops, and local bodies keep their structured control:
conditionals, counted iteration, Boolean literals, explicit stops and the
yields that end a region. Instructions outside the admitted subset are kept as
`unsupported`, so that a rule can refuse them. The carrier fixes no meaning;
`Zkc.Executable.Execution` selects one.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction

/-- A physical value type of `zkc.program/0`: the logical sort and the selected
representation, as in `group:bls12-381.g1@arkworks.g1/0`. -/
structure PhysicalType where
  sort : ValueSort
  representation : String
  deriving DecidableEq, Repr

/-- A static operation parameter: a decoded occurrence template, or text. -/
inductive Parameter where
  | template (template : Template)
  | text (value : String)
  deriving DecidableEq, Repr

/-- Instructions of a local function body or of one of its regions. A
conditional runs one of its two regions on its captured values and binds what
that region yields. An iteration runs its region once for every index from
`lower` up to but excluding `upper`, on the index, the carried values and the
captures, and binds what the last iteration yields, or the initial carried
values when it runs no iteration. A region ends with `yield` and a function
body with `ret`. -/
inductive Step where
  | operation (site binding : String) (parameters : List Parameter) (inputs outputs : List String)
  | constant (site output : String) (value : Bool)
  | cond (site condition : String) (captures : List String) (yes no : List Step)
      (outputs : List String)
  | iterate (site induction lower upper : String) (carried : List (String × String))
      (captures : List String) (body : List Step) (outputs : List String)
  | stop (site reason : String)
  | yield (values : List String)
  | ret (values : List String)
  | unsupported (name : String)
  deriving Repr

structure Function where
  symbol : String
  inputs : List (String × PhysicalType)
  results : List PhysicalType
  body : List Step
  deriving Repr

/-- Participant instructions: a typed receive, a local call, a loop, the yield
that ends a loop body, the final return, or anything else. A loop runs its body
once for every index below the value of `count`, which must not exceed
`maximum`, on the index, the carried values and the captures, and binds what
the last iteration yields, or the initial carried values when the count is
zero. -/
inductive Action where
  | receive (site schema peer output : String) (type : PhysicalType)
  | call (site function : String) (inputs outputs : List String)
  | loop (site count : String) (maximum : Nat) (induction : String)
      (carried : List (String × String)) (captures : List String) (body : List Action)
      (outputs : List String)
  | yield (values : List String)
  | ret (values : List String)
  | unsupported (name : String)
  deriving Repr

/-- A declared operation binding: contract, static arguments, installed
implementation and its exact physical specialization. -/
structure Binding where
  symbol : String
  contract : String
  arguments : List String
  implementation : String
  physicalArguments : List PhysicalType
  deriving DecidableEq, Repr

/-- The validator participant selected by a deployment, with the functions and
bindings of its artifact. -/
structure Validator where
  entry : String
  role : String
  symbol : String
  inputs : List (String × PhysicalType)
  results : List PhysicalType
  body : List Action
  functions : List Function
  bindings : List Binding
  deriving Repr

end Zkc.Executable
