module

public import Zkc.Construction.Participant

@[expose] public section

/-! The executable validator stage of a native proof deployment.

The bridge reads the validator participant that a `zkc.program/0` artifact
selects for the deployment's entry and validator role, together with the local
functions and operation bindings it reaches, into this carrier. It keeps the
artifact's names, sites, physical types and binding records. Occurrence
templates in operation parameters are decoded and re-encoded exactly by the
bridge; every other parameter is kept as text. Instructions outside the
admitted subset are kept as `unsupported`, so that a rule can refuse them.
The carrier fixes no meaning; `Zkc.Executable.Execution` selects one.
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

/-- Instructions of a local function: an operation on a declared binding, the
final return, or anything else. -/
inductive Step where
  | operation (site binding : String) (parameters : List Parameter) (inputs outputs : List String)
  | ret (values : List String)
  | unsupported (name : String)
  deriving DecidableEq, Repr

structure Function where
  symbol : String
  inputs : List (String × PhysicalType)
  results : List PhysicalType
  body : List Step
  deriving DecidableEq, Repr

/-- Participant instructions: a typed receive, a local call, the final return,
or anything else. -/
inductive Action where
  | receive (site schema peer output : String) (type : PhysicalType)
  | call (site function : String) (inputs outputs : List String)
  | ret (values : List String)
  | unsupported (name : String)
  deriving DecidableEq, Repr

/-- A declared operation binding: contract, static arguments and the installed
implementation. -/
structure Binding where
  symbol : String
  contract : String
  arguments : List String
  implementation : String
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
  deriving DecidableEq, Repr

end Zkc.Executable
