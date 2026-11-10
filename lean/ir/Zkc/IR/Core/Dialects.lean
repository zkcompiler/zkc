module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.IR.Core.Types

@[expose] public section

/-! The local and protocol dialects of the core language over the shared `Region`.

The dialects are indexed by the package's operation table, the headers of the
earlier definitions (most recent first) and whether the definition is deployed. An
operation names a catalogue row by a `Var` into the operation table and an earlier
definition by a `Var` into the headers; each variable's type carries the row's
signature and kind or the callee's signature and specification flag. A use of a row
therefore agrees with the row, and a reference points to an earlier definition, by
typing. The callee's row number is the number of headers after it; an operation
row's number is its variable's index.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- One copy of an agreed value among the ports of a protocol: its holder and its
port. -/
structure Copy (ports : List Located) (type : Ty) where
  holder : Nat
  port : Var ports ⟨type, holder⟩
  deriving Repr

/-- An agreement: the inputs, or the outputs, of one protocol that are copies of one
source value held by several roles. The copies have one type by typing. -/
structure Agreement (ports : List Located) where
  type : Ty
  copies : List (Copy ports type)
  deriving Repr

/-- The agreements of a protocol's signature, over its inputs and over its outputs. -/
structure Agreements (inputs outputs : List Located) where
  inputs : List (Agreement inputs)
  outputs : List (Agreement outputs)
  deriving Repr

/-- A signature without agreements. -/
def Agreements.none {inputs outputs : List Located} : Agreements inputs outputs := ⟨[], []⟩

instance {inputs outputs : List Located} : Inhabited (Agreements inputs outputs) := ⟨.none⟩

/-- What a later definition knows of an earlier one: its kind, signature and whether
it is specification-only. The agreements are part of a protocol's signature. -/
inductive Header where
  | function (inputs outputs : List Ty) (specificationOnly : Bool)
  | protocol (roles : Nat) (inputs outputs : List Located) (agreements : Agreements inputs outputs)
      (specificationOnly : Bool)
  deriving Repr, Inhabited

/-- Local operations: the computation of functions and of one role. `stop` is
`Region.stop`. The flag `deployed` forbids calling a specification-only function. -/
inductive LocalOp (operations : List OperationSignature) (headers : List Header) (deployed : Bool) where
  /-- A pure or partial catalogue operation, by its row. -/
  | op {inputs outputs : List Ty} {kind : OperationKind}
      (row : Var operations ⟨inputs, outputs, kind⟩) (computes : kind.computes = true)
  /-- A call of an earlier function. -/
  | call {inputs outputs : List Ty} {specificationOnly : Bool}
      (callee : Var headers (.function inputs outputs specificationOnly))
      (permitted : (deployed && specificationOnly) = false)
  /-- `if`: a condition and captures; two regions over the captures. -/
  | conditional (captures outputs : List Ty)
  /-- `loop(m)`: a count, carried values and captures; one region from the iteration
  number, the carried values and the captures to the carried values. -/
  | loop (maximum : Nat) (carried captures : List Ty)
  /-- `guard(reason)`: stops with the authored reason when the condition is false. -/
  | guard (reason : Reason)

namespace LocalOp

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

@[reducible] def arguments : LocalOp operations headers deployed → List Ty
  | .op (inputs := inputs) .. => inputs
  | .call (inputs := inputs) .. => inputs
  | .conditional captures _ => .bool :: captures
  | .loop _ carried captures => .index :: (carried ++ captures)
  | .guard _ => [.bool]

@[reducible] def results : LocalOp operations headers deployed → List Ty
  | .op (outputs := outputs) .. => outputs
  | .call (outputs := outputs) .. => outputs
  | .conditional _ outputs => outputs
  | .loop _ carried _ => carried
  | .guard _ => []

@[reducible] def regions : LocalOp operations headers deployed → List (List Ty × List Ty)
  | .conditional captures outputs => [(captures, outputs), (captures, outputs)]
  | .loop _ carried captures => [(.index :: (carried ++ captures), carried)]
  | .op .. | .call .. | .guard _ => []

end LocalOp

def LocalDialect (operations : List OperationSignature) (headers : List Header) (deployed : Bool) :
    Dialect where
  Ty := Ty
  Op := LocalOp operations headers deployed
  arguments := LocalOp.arguments
  results := LocalOp.results
  regions := LocalOp.regions

/-- Protocol operations over located types. A local operation performed by one role
keeps its nested regions as local regions inside the operation. -/
inductive ProtocolOp (operations : List OperationSignature) (headers : List Header) (deployed : Bool) where
  /-- `at(r, ℓ)`: role `r` performs the local operation `ℓ` on values it holds. -/
  | «at» (role : Nat) (op : LocalOp operations headers deployed)
      (bodies : Regions (LocalDialect operations headers deployed) op.regions)
  /-- `exchange(s, r, site)`: `s` sends a value to `r`. -/
  | exchange (sender receiver site : Nat) (type : Ty)
  /-- `draw(o, R, site, law)`: `o` draws a public coin and announces it to `R`. -/
  | draw (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩)
  /-- `sample(o, site, law)`: `o` samples a secret. -/
  | sample (owner site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩)
  /-- `repeat(P, m)`: each participant holds a count; one region from the carried
  values and captures to the carried values. -/
  | «repeat» (participants : List Nat) (maximum : Nat) (carried captures : List Located)
  /-- `branch(P)`: each participant holds a condition; two regions over the captures.
  The outputs are held by participants. -/
  | branch (participants : List Nat) (captures outputs : List Located)
      (covered : Located.heldBy participants outputs = true)
  /-- `apply(d, ρ, site)`: the caller's roles `ρ(0), ρ(1), …` run protocol `d`. -/
  | apply {roles : Nat} {inputs outputs : List Located} {agreements : Agreements inputs outputs}
      {specificationOnly : Bool}
      (callee : Var headers (.protocol roles inputs outputs agreements specificationOnly))
      (roleMap : RoleMap) (site : Nat)
      (permitted : (deployed && specificationOnly) = false)

namespace ProtocolOp

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

@[reducible] def arguments : ProtocolOp operations headers deployed → List Located
  | .at role op _ => Located.atRole role op.arguments
  | .exchange sender _ _ type => [⟨type, sender⟩]
  | .draw owner _ _ (inputs := inputs) _ => Located.atRole owner inputs
  | .sample owner _ (inputs := inputs) _ => Located.atRole owner inputs
  | .repeat participants _ carried captures =>
      Located.ofRoles .index participants ++ (carried ++ captures)
  | .branch participants captures _ _ => Located.ofRoles .bool participants ++ captures
  | .apply (inputs := inputs) _ roleMap .. => inputs.map (Located.rename roleMap)

@[reducible] def results : ProtocolOp operations headers deployed → List Located
  | .at role op _ => Located.atRole role op.results
  | .exchange _ receiver _ type => [⟨type, receiver⟩]
  | .draw owner receivers _ (output := output) _ =>
      ⟨output, owner⟩ :: Located.ofRoles output receivers
  | .sample owner _ (output := output) _ => [⟨output, owner⟩]
  | .repeat _ _ carried _ => carried
  | .branch _ _ outputs _ => outputs
  | .apply (outputs := outputs) _ roleMap .. => outputs.map (Located.rename roleMap)

@[reducible] def regions : ProtocolOp operations headers deployed →
    List (List Located × List Located)
  | .repeat _ _ carried captures => [(carried ++ captures, carried)]
  | .branch _ captures outputs _ => [(captures, outputs), (captures, outputs)]
  | .at .. | .exchange .. | .draw .. | .sample .. | .apply .. => []

end ProtocolOp

def ProtocolDialect (operations : List OperationSignature) (headers : List Header) (deployed : Bool) :
    Dialect where
  Ty := Located
  Op := ProtocolOp operations headers deployed
  arguments := ProtocolOp.arguments
  results := ProtocolOp.results
  regions := ProtocolOp.regions

/-- A definition typed over the operation table and the headers of the earlier
definitions. A deployed definition (not specification-only) applies and calls no
specification-only one. A protocol states its role count and its agreements. -/
inductive Definition (operations : List OperationSignature) (headers : List Header) :
    Header → Type where
  | function {inputs outputs : List Ty} (specificationOnly : Bool)
      (body : Region (LocalDialect operations headers (!specificationOnly)) inputs outputs) :
      Definition operations headers (.function inputs outputs specificationOnly)
  | protocol {inputs outputs : List Located} (roles : Nat) (agreements : Agreements inputs outputs)
      (specificationOnly : Bool)
      (body : Region (ProtocolDialect operations headers (!specificationOnly)) inputs outputs) :
      Definition operations headers (.protocol roles inputs outputs agreements specificationOnly)

end Zkc.Core

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.LocalOp.arguments
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.LocalOp.results
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.LocalOp.regions
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.arguments
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.results
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.regions
