module

public import Zkc.Source.Common.Scalar

@[expose] public section

/-! Role-local validator programs after native transcript construction.

The bridge decodes the compiler's `zkc.constructed-participant/0` export into
this carrier. Every exported operation keeps its operand references and result
sorts; transcript operations keep their decoded occurrence origins. References
are absolute positions: inputs first, then every result in execution order.
The carrier fixes no meaning for transcript operations; a separate model selects
one.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source.Common.Native

/-- A flat native occurrence template: the original entry and the ordered event
fields, with no application or repeat steps and no dynamic coordinates. The
native canonical encoding of
`["zkc.native-origin-template/0", entry, [], [], event]` is injective in these
two fields; the bridge decodes and re-encodes it exactly. -/
structure Origin where
  entry : String
  event : List String
  deriving DecidableEq, Repr

namespace Origin

/-- A message occurrence; its schema is the original source site. -/
def message (entry site sender receiver : String) : Origin :=
  ⟨entry, ["message", entry, site, site, sender, receiver]⟩

/-- A field challenge replacing the validator's `draw` query. -/
def query (entry site port contract owner : String) : Origin :=
  ⟨entry, ["query", entry, site, port, contract, "draw", owner]⟩

end Origin

/-- Sorts of exported values: scalar data, the affine transcript capability of
one suite, and occurrence coordinates. -/
inductive ValueSort where
  | data (ty : Ty)
  | transcript (suite : String)
  | indices
  deriving DecidableEq, Repr

/-- Exported operations, as decoded from operation names, operation bindings and
attributes. Anything outside this vocabulary is retained as `unsupported`. -/
inductive Operation where
  | receive (site schema peer : String) (ty : Ty)
  | send (site schema peer : String)
  | indicesEmpty
  | observe (suite : String) (origin : Origin)
  | challenge (suite field : String) (origin : Origin)
  | calculate (op : Op)
  | unsupported (name : String)
  deriving DecidableEq, Repr

structure Instruction where
  operation : Operation
  operands : List Nat
  results : List ValueSort
  deriving DecidableEq, Repr

/-- The native deployment policy exactly as exported: entry, producer and
validator roles, acceptance index, suite, replaced services, public inputs,
ordered query/delivery site pairs, framing and construction selector. -/
structure Policy where
  entry : String
  producer : String
  validator : String
  acceptance : Nat
  suite : String
  services : List Nat
  publicInputs : List Nat
  draws : List (String × String)
  format : String
  construction : String
  deriving DecidableEq, Repr

/-- One exported validator participant. `source` and `candidate` identify the
original MLIR bytes and the checked candidate print. -/
structure Participant where
  source : String
  candidate : String
  policy : Policy
  symbol : String
  inputs : List ValueSort
  outputs : List ValueSort
  instructions : List Instruction
  returned : List Nat
  deriving DecidableEq, Repr

end Zkc.Construction
