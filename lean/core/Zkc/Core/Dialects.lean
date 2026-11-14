module

public import Zkc.Core.Builtin

public section

/-! The local and protocol dialects of the core language over the shared `Region`.

A program is its functions followed by its protocols. A function may call the functions
before it. A protocol may call every function and apply the protocols before it.

The local dialect is indexed by the package's operation table and the headers of the
functions it may call. The protocol dialect is indexed by the same two and by the
headers of the protocols it may apply. A local operation therefore does not mention a
protocol header: a step that changes the signatures of protocols re-types protocol
operations and leaves every local operation, every local region and every function
definition as it is, by typing.

An operation names a catalogue row, a function or a protocol by a reference into the
corresponding list (the most recent first); the reference's type carries the row's
signature and kind or the callee's header. A use therefore agrees with what it names
by typing.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- One copy of an agreed value among the ports of a protocol: its holder and its
port. -/
structure Copy (ports : List Located) (type : Ty) where
  holder : Nat
  port : Var ports ⟨type, holder⟩
  deriving Repr, DecidableEq

/-- An agreement: the inputs, or the outputs, of one protocol that are copies of one
source value held by several roles. The copies have one type by typing, and there is at
least one. -/
structure Agreement (ports : List Located) where
  type : Ty
  first : Copy ports type
  others : List (Copy ports type)
  deriving Repr, DecidableEq

/-- The copies of an agreement. -/
@[expose] def Agreement.copies {ports : List Located} (agreement : Agreement ports) :
    List (Copy ports agreement.type) :=
  agreement.first :: agreement.others

/-- The agreements of a protocol's signature, over its inputs and over its outputs. -/
structure Agreements (inputs outputs : List Located) where
  inputs : List (Agreement inputs)
  outputs : List (Agreement outputs)
  deriving Repr, DecidableEq

/-- A signature without agreements. -/
def Agreements.none {inputs outputs : List Located} : Agreements inputs outputs := ⟨[], []⟩

instance {inputs outputs : List Located} : Inhabited (Agreements inputs outputs) := ⟨.none⟩

/-- What a caller knows of a function: its signature and whether it is
specification-only. -/
structure FunctionHeader where
  inputs : List Ty
  outputs : List Ty
  specificationOnly : Bool
  deriving Repr, Inhabited, DecidableEq

/-- What a caller knows of a protocol: its role count, its signature with the holders
and agreements, and whether it is specification-only. -/
structure ProtocolHeader where
  roles : Nat
  inputs : List Located
  outputs : List Located
  agreements : Agreements inputs outputs
  specificationOnly : Bool
  deriving Repr, Inhabited

/-- The tag of a shared choice: a condition, which selects one of two regions, the number
of one of `count` regions, a value of `fin count`, or a value of a variant, whose
alternative selects the region of that alternative. A variant names its declaration by its
number and carries the payload types of its alternatives. -/
inductive ChoiceTag where
  | condition
  | arm (count : Nat)
  | alternative (declaration : Nat) (alternatives : List Ty)
  deriving Repr, Inhabited, DecidableEq

/-- The type of the tag that each participant holds. -/
@[expose, reducible] def ChoiceTag.type : ChoiceTag → Ty
  | .condition => .bool
  | .arm count => .fin count
  | .alternative declaration alternatives => .variant declaration alternatives

/-- The number of regions. -/
@[expose, reducible] def ChoiceTag.arms : ChoiceTag → Nat
  | .condition => 2
  | .arm count => count
  | .alternative _ alternatives => alternatives.length

/-- The signatures of the regions of a shared choice, in the order of the values of the
tag. The regions of a condition and of an arm number all go from the captures to the
outputs. The region of an alternative of a variant takes first one copy of the payload of
that alternative per participant, in the order of the participants and each held by its
participant, and then the captures; a variant without alternatives has no region. -/
@[expose, reducible] def ChoiceTag.regions (participants : List Nat)
    (captures outputs : List Located) : ChoiceTag → List (List Located × List Located)
  | .condition => List.replicate 2 (captures, outputs)
  | .arm count => List.replicate count (captures, outputs)
  | .alternative _ alternatives =>
      alternatives.map fun payload => (Located.ofRoles payload participants ++ captures, outputs)

/-- The signatures of the regions of the choice of one role. The region of an alternative
of a variant takes the role's payload of that alternative, and then the captures, as a
region of a `match` does. -/
@[expose, reducible] def ChoiceTag.ownRegions (captures outputs : List Ty) :
    ChoiceTag → List (List Ty × List Ty)
  | .condition => List.replicate 2 (captures, outputs)
  | .arm count => List.replicate count (captures, outputs)
  | .alternative _ alternatives => alternatives.map fun payload => (payload :: captures, outputs)

/-- How the count of a `loop` is given: a number of the operation, or a value with an
optional maximum. -/
inductive LoopCount where
  | static (count : Nat)
  | runtime (maximum : Option Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The size of the sequence that a loop collects into: its count when the operation has
it, a property of the value otherwise. -/
@[expose, reducible] def LoopCount.size : LoopCount → Option Nat
  | .static count => some count
  | .runtime _ => none

/-- The types of the sequences that a loop collects into, one per collected type. -/
@[expose, reducible] def collectedSequences (size : Option Nat) (collected : List Ty) : List Ty :=
  collected.map fun type => .seq type size

/-- How the count of a `repeat` is given: a number of the operation, or a value that each
participant holds, with its maximum. -/
inductive RepeatCount where
  | static (count : Nat)
  | runtime (maximum : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The count operands of a `repeat`: none for a count of the operation, and one `nat`
held by each participant for a count that is a value. -/
@[expose, reducible] def RepeatCount.operands (participants : List Nat) :
    RepeatCount → List Located
  | .static _ => []
  | .runtime _ => Located.ofRoles .nat participants

/-- The size of the sequence that a `repeat` collects into: its count when the operation
has it, a property of the value otherwise. -/
@[expose, reducible] def RepeatCount.size : RepeatCount → Option Nat
  | .static count => some count
  | .runtime _ => none

/-- The located types of the sequences that a `repeat` collects into, one per collected
value, each held by the holder of the value. -/
@[expose, reducible] def collectedSequencesAt (size : Option Nat) (collected : List Located) :
    List Located :=
  collected.map fun located => ⟨.seq located.type size, located.holder⟩

/-- The count operand of the loop of one role: none for a count of the operation. -/
@[expose, reducible] def RepeatCount.ownOperands : RepeatCount → List Ty
  | .static _ => []
  | .runtime _ => [.nat]

/-- Local operations: the computation of functions and of one role. `stop` is
`Region.stop`. The flag `deployed` forbids calling a specification-only function. -/
inductive LocalOp (operations : List OperationSignature) (functions : List FunctionHeader)
    (deployed : Bool) where
  /-- A pure or restricted catalogue operation, by its row. -/
  | op {inputs outputs : List Ty} {kind : OperationKind}
      (row : Var operations ⟨inputs, outputs, kind⟩)
      (applies : OperationSignature.applies ⟨inputs, outputs, kind⟩ = true)
  /-- A call of an earlier function. -/
  | call {header : FunctionHeader} (callee : Var functions header)
      (permitted : (deployed && header.specificationOnly) = false)
  /-- `if`: a condition and captures; two regions over the captures. -/
  | conditional (captures outputs : List Ty)
  /-- `match`: a value of a variant and captures; one region per alternative, from the
  payload of that alternative and the captures. No region sees the payload of another
  alternative, and a variant without alternatives has no region. -/
  | «match» (declaration : Nat) (alternatives captures outputs : List Ty)
  /-- `loop`: carried values and captures, after the count when it is a value; one region
  from the iteration number, the carried values and the captures to one value of each
  collected type and then the carried values. Its results are, per collected type, the
  values of the iterations in order, and then the carried values: a sized sequence when the
  count is a number of the operation, an unsized one when it is a value. -/
  | loop (count : LoopCount) (carried collected captures : List Ty)
  /-- `guard(reason)`: stops with the authored reason when the condition is false. -/
  | guard (reason : Reason)
  /-- A literal value. -/
  | literal (value : Literal)
  /-- An operation the core owns, on values of the types whose values the core fixes. -/
  | builtin (operation : Builtin)

namespace LocalOp

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

@[expose, reducible] def arguments : LocalOp operations functions deployed → List Ty
  | .op (inputs := inputs) .. => inputs
  | .call (header := header) .. => header.inputs
  | .conditional captures _ => .bool :: captures
  | .match declaration alternatives captures _ =>
      .variant declaration alternatives :: captures
  | .loop (.static _) carried _ captures => carried ++ captures
  | .loop (.runtime _) carried _ captures => .nat :: (carried ++ captures)
  | .guard _ => [.bool]
  | .literal _ => []
  | .builtin operation => operation.arguments

@[expose, reducible] def results : LocalOp operations functions deployed → List Ty
  | .op (outputs := outputs) .. => outputs
  | .call (header := header) .. => header.outputs
  | .conditional _ outputs => outputs
  | .match _ _ _ outputs => outputs
  | .loop count carried collected _ => collectedSequences count.size collected ++ carried
  | .guard _ => []
  | .literal value => [value.type]
  | .builtin operation => operation.results

@[expose, reducible] def regions : LocalOp operations functions deployed → List (List Ty × List Ty)
  | .conditional captures outputs => [(captures, outputs), (captures, outputs)]
  | .match _ alternatives captures outputs =>
      alternatives.map fun payload => (payload :: captures, outputs)
  | .loop _ carried collected captures =>
      [(.nat :: (carried ++ captures), collected ++ carried)]
  | .op .. | .call .. | .guard _ | .literal _ | .builtin _ => []

end LocalOp

@[expose, reducible] def LocalDialect (operations : List OperationSignature)
    (functions : List FunctionHeader) (deployed : Bool) : Dialect where
  Ty := Ty
  Op := LocalOp operations functions deployed
  arguments := LocalOp.arguments
  results := LocalOp.results
  regions := LocalOp.regions

/-- Protocol operations over located types. A local operation performed by one role
keeps its nested regions as local regions inside the operation. -/
inductive ProtocolOp (operations : List OperationSignature) (functions : List FunctionHeader)
    (protocols : List ProtocolHeader) (deployed : Bool) where
  /-- `at(r, ℓ)`: role `r` performs the local operation `ℓ` on values it holds. -/
  | «at» (role : Nat) (op : LocalOp operations functions deployed)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions)
  /-- `exchange(s, r, site)`: `s` sends a value to `r`. -/
  | exchange (sender receiver site : Nat) (type : Ty)
  /-- `draw(o, R, site, law)`: `o` draws a public coin and announces it to `R`. The output
  type of the law is populated: there is a coin to draw. -/
  | draw (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
  /-- `sample(o, site, law)`: `o` samples a secret. The output type of the law is
  populated. -/
  | sample (owner site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
  /-- `repeat(P, c)`: carried values and captures, after a count held by each participant
  when the count is a value; one region from the iteration number, which each participant
  holds, the carried values and the captures to one value per collected entry and then the
  carried values. A collected value is held by a participant. The results are, per
  collected entry, the values of the iterations in order at its holder, and then the carried
  values: a sized sequence when the count is a number of the operation, an unsized one when
  it is a value. -/
  | «repeat» (participants : List Nat) (count : RepeatCount)
      (carried collected captures : List Located)
      (covered : Located.heldBy participants collected = true)
  /-- `choose(P)`: each participant holds a tag; one region per value of the tag, over the
  captures. The outputs are held by participants. With a condition as the tag it is the
  branch: the first region for `false`, the second for `true`. With a variant as the tag
  there is one region per alternative, which takes each participant's copy of the payload
  of that alternative before the captures. -/
  | choose (participants : List Nat) (tag : ChoiceTag) (captures outputs : List Located)
      (covered : Located.heldBy participants outputs = true)
  /-- `apply(d, ρ, site)`: the caller's roles `ρ(0), ρ(1), …` run protocol `d`. -/
  | apply {header : ProtocolHeader} (callee : Var protocols header) (roleMap : RoleMap)
      (site : Nat) (permitted : (deployed && header.specificationOnly) = false)

namespace ProtocolOp

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

@[expose, reducible] def arguments : ProtocolOp operations functions protocols deployed → List Located
  | .at role op _ => Located.atRole role op.arguments
  | .exchange sender _ _ type => [⟨type, sender⟩]
  | .draw owner _ _ (inputs := inputs) _ _ => Located.atRole owner inputs
  | .sample owner _ (inputs := inputs) _ _ => Located.atRole owner inputs
  | .repeat participants count carried _ captures _ =>
      count.operands participants ++ (carried ++ captures)
  | .choose participants tag captures _ _ => Located.ofRoles tag.type participants ++ captures
  | .apply (header := header) _ roleMap .. => header.inputs.map (Located.rename roleMap)

@[expose, reducible] def results : ProtocolOp operations functions protocols deployed → List Located
  | .at role op _ => Located.atRole role op.results
  | .exchange _ receiver _ type => [⟨type, receiver⟩]
  | .draw owner receivers _ (output := output) _ _ =>
      ⟨output, owner⟩ :: Located.ofRoles output receivers
  | .sample owner _ (output := output) _ _ => [⟨output, owner⟩]
  | .repeat _ count carried collected _ _ => collectedSequencesAt count.size collected ++ carried
  | .choose _ _ _ outputs _ => outputs
  | .apply (header := header) _ roleMap .. => header.outputs.map (Located.rename roleMap)

@[expose, reducible] def regions : ProtocolOp operations functions protocols deployed →
    List (List Located × List Located)
  | .repeat participants _ carried collected captures _ =>
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]
  | .choose participants tag captures outputs _ => tag.regions participants captures outputs
  | .at .. | .exchange .. | .draw .. | .sample .. | .apply .. => []

end ProtocolOp

@[expose, reducible] def ProtocolDialect (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader) (deployed : Bool) :
    Dialect where
  Ty := Located
  Op := ProtocolOp operations functions protocols deployed
  arguments := ProtocolOp.arguments
  results := ProtocolOp.results
  regions := ProtocolOp.regions

/-- A function typed over the operation table and the headers of the functions before
it. A deployed definition (not specification-only) calls no specification-only one.
The inputs are bound in order. -/
structure FunctionDefinition (operations : List OperationSignature)
    (functions : List FunctionHeader) (header : FunctionHeader) where
  body : Region (LocalDialect operations functions (!header.specificationOnly))
    (bindAll [] header.inputs) header.outputs

/-- A protocol typed over the operation table, the headers of every function and the
headers of the protocols before it. -/
structure ProtocolDefinition (operations : List OperationSignature)
    (functions : List FunctionHeader) (protocols : List ProtocolHeader)
    (header : ProtocolHeader) where
  body : Region (ProtocolDialect operations functions protocols (!header.specificationOnly))
    (bindAll [] header.inputs) header.outputs

end Zkc.Core
