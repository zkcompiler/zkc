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
value-counted loops and their selected control (conditionals and matches),
each with its explicit capture rows, and local bodies keep their structured
control: conditionals, counted iteration, Boolean literals, explicit stops and
the yields that end a region. Instructions outside the admitted subset are kept
as `unsupported`, so that a rule can refuse them. The carrier fixes no meaning;
`Zkc.Executable.Execution` selects one.

A participant loop body and every arm of a participant conditional or match is
a nested lexical environment: it sees only its formals (the loop's induction,
carried formals and capture formals, or the arm's payload bindings and capture
formals), and its bindings are not visible after it. Sites, message schemas
and service ports stay participant-wide.

`ProgramArtifact` carries a whole artifact in the same vocabulary, for the
structural admission of `Zkc.Executable.ProgramAdmission`.
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
body with `ret`. Local control keeps capture names: scoped local regions
canonicalize aliased captures before emission. -/
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

/-- One capture row `[formal, parent]` of a participant loop, conditional or
match: the body binds `formal` to the value of `parent` in the enclosing body.
Each row keeps its own formal, so two rows may share a parent; that is admitted
only for a copyable parent, and an affine value is never duplicated this way. -/
structure Capture where
  formal : String
  parent : String
  deriving DecidableEq, Repr

/-- Participant instructions: a typed receive, a local call, a loop, a selected
conditional or match, the yield that ends a loop body or an arm, the final
return, or anything else. A loop runs its body once for every index below the
value of `count`, which must not exceed `maximum`, on the index, the carried
values and the capture formals, and binds what the last iteration yields, or
the initial carried values when the count is zero. A conditional runs only the
arm its Boolean condition selects (`yes` for true), and a match only the arm of
the alternative its variant input carries. Match arms are `(alternative,
payload bindings, body)` in declaration order. An arm sees its payload bindings
and capture formals, and what it yields binds the outputs. -/
inductive Action where
  | receive (site schema peer output : String) (type : PhysicalType)
  | call (site function : String) (inputs outputs : List String)
  | loop (site count : String) (maximum : Nat) (induction : String)
      (carried : List (String × String)) (captures : List Capture) (body : List Action)
      (outputs : List String)
  | cond (site condition : String) (captures : List Capture) (yes no : List Action)
      (outputs : List String)
  | select (site input : String) (captures : List Capture)
      (arms : List (String × List String × List Action)) (outputs : List String)
  | yield (values : List String)
  | ret (values : List String)
  | unsupported (name : String)
  deriving Repr

/-- A declared operation binding, including the physical specialization of its
installed implementation. -/
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

/-- A participant's service port: its name, its service contract and the
participant input it stands for. -/
structure ParticipantService where
  name : String
  contract : String
  input : Nat
  deriving DecidableEq, Repr

/-- A participant definition of a program: its symbol, the entry instance and
role it serves, its interface and body, and its service ports. -/
structure ParticipantDefinition where
  symbol : String
  entry : String
  role : String
  inputs : List (String × PhysicalType)
  results : List PhysicalType
  body : List Action
  services : List ParticipantService
  deriving Repr

/-- An entry and its ordered role map to participant symbols. -/
structure ProgramEntry where
  name : String
  roles : List (String × String)
  deriving DecidableEq, Repr

/-- A whole `zkc.program/0` artifact. -/
structure ProgramArtifact where
  bindings : List Binding
  functions : List Function
  participants : List ParticipantDefinition
  entries : List ProgramEntry
  deriving Repr

end Zkc.Executable
