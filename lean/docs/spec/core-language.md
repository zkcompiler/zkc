# Core language: formal model

The [core language](../../../docs/spec/core/README.md) has a formal model in the IR
package. A `zkc.core/0` package is imported into typed Lean terms that the kernel
checks, and every protocol denotes, for every side, a `PIR.Process` over one effect
signature. Statements hold for an arbitrary model; laws are hypotheses about the
model, stated on rows that are named by their catalogue identity.

| Module | Content |
|---|---|
| `Zkc.IR.Core.Types` | types and their values, located types, sides, the `Held` family, operation rows, authored reasons, models, catalogue identities, effects |
| `Zkc.IR.Core.Dialects` | agreements, headers, the local and protocol dialects over the shared `Region`, definitions |
| `Zkc.IR.Core.WellFormed` | residual well-formedness, decided by the kernel; programs |
| `Zkc.IR.Core.Meaning` | the meaning of functions and of protocols for a side; program tables; the proposition of an agreement |
| `Zkc.IR.Core.Laws` | equations of the meaning, one operation at a time |
| `Zkc.Tools.IR.Core.Import` | the `import_core` command |
| `Zkc.Tests.IR.Core.*` | the Schnorr, Sumcheck and opening packages, semantic controls, refusals |

## Types, holders and sides

`Ty` is `unit | bool | index | nominal n | array T | tuple Ts | variant Ts`. Its
values are `Ty.Value Carrier`, where a model supplies `Carrier n` for nominal row
`n`. A located type `⟨T, r⟩ : Located` has one holder. There are no multi-role and
no optional values.

A side is a membership function `Side := Nat → Bool`. `Side.ofMask m` is the side of
the set bits of `m`, so a literal side applied to a literal role reduces to `true`
or `false`. The value of `⟨T, r⟩` for a side is

```lean
def Held (X : Type) : Bool → Type
  | true => X
  | false => PUnit

def SideValue (model : Model) (side : Side) : Located → Type
  | ⟨type, holder⟩ => Held (model.Value type) (side holder)
```

For a literal side, `SideValue` reduces to the value type or to `PUnit`; no cast,
optional value or run-time presence test appears in a side's process. The
transports between held and plain values (`Held.of`, `Held.value`, `Held.absent`,
`presentValues`, `holdValues`) match on the membership first, so they reduce away
at a literal side whatever the form of the value.

## Models, reasons and effects

A model gives the carriers and a meaning to every pure and partial operation row:

```lean
inductive Reason where
  | reject | abort | exhausted | refused

structure Model where
  Carrier : Nat → Type
  pure : (row : OperationRow) → Values (Ty.Value Carrier) row.inputs → Values (Ty.Value Carrier) row.outputs
  «partial» : (row : OperationRow) → Values (Ty.Value Carrier) row.inputs →
    Except Reason (Values (Ty.Value Carrier) row.outputs)
```

`Reason` is the type of the authored reasons; `Reason.stop` maps it into the shared
`PIR.Stop`, whose fifth reason is `incomplete`. A partial row and a `guard` stop
with a `Reason`, so neither can name `incomplete`: for every model and every
program, the reason `incomplete` in a side's process comes from the agreement rule
and from nowhere else. No hypothesis about the model is needed
(`Reason.stop_ne_incomplete`; the control `decrement_never_incomplete` states it for
a partial row and every model).

`OperationRow` is the row number with its signature. An operation names its row by
a variable into the package's operation table; `OperationRow.of row` and
`SamplingRow.of law` are the keys under which the model and the effects see it. A
sampling row has no meaning: the reply of a `draw` or `sample` is unconstrained.
The effect signature `Effects model` depends on the model only, so a callee's
process is a caller's process without renaming:

```lean
inductive Effect (Value : Ty → Type) where
  | send (site : Site) (type : Ty) (value : Value type)
  | receive (site : Site) (type : Ty)
  | draw (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  | sample (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  | read (site : Site) (type : Ty) (position : Value type)
```

The replies are `PUnit`, `Value type`, the law's output value, the law's output
value and `PUnit`. A `Site` is the definition's row number and the local site number.
`OnlyEffects allowed process` and `NeverStops reason process` are predicates over
every reply of a process.

## Catalogue identities

A row of the type table or of the operation table is a catalogue name applied to
static arguments. The model keeps these identities as data:

```lean
inductive Static where
  | domain (name : String) | nat (value : Nat) | type (type : Ty)

structure CatalogueRow where
  name : String
  statics : List Static

structure Catalogue where
  types : List CatalogueRow
  operations : List CatalogueRow
```

No typing rule, residual condition or meaning inspects a `Catalogue`; the kernel
never compares two of its strings. The importer adds it per package and names
every operation row by its identity (see [Importer](#importer)).

## Dialects, definitions and programs

Both dialects are indexed by the package's operation table
(`List OperationSignature`: inputs, outputs and kind of every row), the headers of
the earlier definitions, most recent first, and whether the definition is deployed.

- `LocalOp`: `op` (a `Var` into the operation table whose type carries the row's
  signature and kind, with a proof that the kind computes), `call` (a `Var` into the
  headers), `conditional`, `loop`, `guard` (with a `Reason`). `stop` is
  `Region.stop`, which names a `PIR.Stop`.
- `ProtocolOp`: `at r ℓ bodies` (role `r` performs local operation `ℓ`, whose nested
  regions are local regions carried by the operation), `exchange`, `draw` and
  `sample` (a `Var` to a sampling row with one output), `repeat`, `branch` (with a
  proof that participants hold the outputs), `apply` (a `Var` into the headers and a
  role map).

A header is what a later definition knows of an earlier one. A protocol's header
carries its agreements, which are part of its signature:

```lean
structure Copy (ports : List Located) (type : Ty) where
  holder : Nat
  port : Var ports ⟨type, holder⟩

structure Agreement (ports : List Located) where
  type : Ty
  copies : List (Copy ports type)

structure Agreements (inputs outputs : List Located) where
  inputs : List (Agreement inputs)
  outputs : List (Agreement outputs)

inductive Header where
  | function (inputs outputs : List Ty) (specificationOnly : Bool)
  | protocol (roles : Nat) (inputs outputs : List Located) (agreements : Agreements inputs outputs)
      (specificationOnly : Bool)
```

A copy is a typed variable into the ports, so the copies of one agreement have one
type by typing. A `Definition operations headers h` is a function or a protocol
whose body is a `Region` of the corresponding dialect. A `Program operations
headers` is built by `Program.snoc earlier definition wellFormed`, where
`wellFormed : definition.violation = none`.

## Well-formedness

Typing fixes the first group of conditions. The residual conditions are decided by
`Definition.violation`, which returns the first violated one by name; a program
accepts a definition only with `definition.violation = none`, so the kernel decides
them once for every definition it accepts.

| Condition | Enforced by |
|---|---|
| operand types and holders, closed regions | typing of `Region` |
| references to earlier definitions | typing: `Var` into the headers |
| a use of a row agrees with its signature and kind | typing: `Var` into the operation table; `op` requires a computing kind, `draw`/`sample` a sampling row with one output |
| the reason of a `guard` is an authored reason | typing: `Reason` |
| a deployed definition calls or applies no specification-only one | typing: proof field `(deployed && specificationOnly) = false` |
| the outputs of a `branch` are held by its participants | typing: proof field `Located.heldBy` |
| the ports of an agreement have one type | typing: `Copy` |
| a protocol has a role | `Violation.noRole` |
| holders, owners, participants and role-map entries are below the role count | `Violation.roleOutOfRange` |
| a `repeat` or `branch` has a participant | `Violation.noParticipant` |
| a `repeat` or `branch` lists each participant once | `Violation.repeatedParticipant` |
| every role that an operation inside a `repeat` or `branch` names is a participant: an owner, a sender, a receiver, the receivers of a draw, the participants of a nested `repeat` or `branch`, the entries of a role map | `Violation.roleOutsideParticipants` |
| every value that enters or leaves a `repeat` or `branch` is held by a participant | `Violation.valueOutsideParticipants` |
| the sender and the receiver of an `exchange` differ | `Violation.exchangeToSelf` |
| the receivers of a `draw` increase strictly | `Violation.receiversNotIncreasing` |
| the owner of a `draw` is not one of its receivers | `Violation.ownerReceives` |
| a role map has one entry per formal role of the callee | `Violation.roleMapLength` |
| a role map is injective | `Violation.roleMapNotInjective` |
| the sites of a definition are below their number: no gap | `Violation.siteGap` |
| no two operations of a definition share a site | `Violation.repeatedSite` |
| a protocol region contains no `stop` | `Violation.protocolStop` |
| the reason of a `stop` is an authored reason | `Violation.reservedReason` |
| the copies of an agreement have different holders | `Violation.agreementHolders` |
| the agreements of a signature name each port at most once | `Violation.agreementPorts` |

`ProtocolOp.roles` lists every role an operation names, and
`ProtocolOp.violation` evaluates the condition lists of one operation
(`actingRoles`, `exchangeConditions`, `drawConditions`, `participantConditions`,
`roleMapConditions`); `portConditions` and `agreementConditions` cover the
signature. One pass over the body, `protocolRegionSites`, checks every operation
and collects the sites; `sitesViolation` then decides that the `k` sites are
`0 … k−1`, each once: every site is below `k` and none repeats. A site is compared
with `k` before its bit is set in the mask of used sites, so no numeral is larger
than the definition.

Points that the model settles:

- **Empty participant lists are refused.** A `repeat` or `branch` without a
  participant has no role that holds its count or condition, and its regions can
  contain no operation.
- **Protocols without a role are refused.** A computation without roles is a
  function.
- **Sites are unique across regions and branch arms.** The two arms of a `branch`
  and a nested region use sites of the one numbering of their definition.
- **A local region inside `at` may stop.** `at r (if …)` carries local regions,
  whose `stop` names an authored reason; the protocol region itself has no `stop`.
- **The reason of a `stop` is a residual condition**, because `Region.stop` of the
  shared program package takes a `PIR.Stop`. The reason of a `guard` and of a
  partial row is authored by typing.
- **Agreements name each port at most once** over the inputs and over the outputs
  of a signature, which includes the ports of one agreement; an agreement without a
  port has no type and is refused by the importer.

## Meaning

`Definition.meaning model table` interprets a definition given the meanings of the
earlier ones; `Program.table` and `Program.meaning` build the table and the meaning
of the last definition. A function denotes
`Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)`
and performs no effect. A protocol denotes

```lean
(side : Side) → Values (SideValue model side) inputs →
  PIR.Process (Effects model) (Values (SideValue model side) outputs)
```

Each operation's side meaning is a step function of the memberships of the roles it
concerns, passed as `Bool` arguments:

- `at(r, ℓ)`: the local meaning of `ℓ` when `r` is in the side, otherwise unit results;
- `exchange(s, r)`: the operand, `send`, `receive` and reply, or nothing;
- `draw(o, R)`: with `o` in the side, one `draw` whose reply is every copy in the
  side; with `o` outside, each receiver in the side performs its own `receive`, in
  order, and holds its own reply;
- `sample(o)`: `sample` when `o` is in the side;
- `repeat(P, m)` and `branch(P)`: with no participant in the side, nothing; when the
  copies of the count or condition held by the participants in the side differ,
  `halt .incomplete`; otherwise `repeatProcess` (`PIR.repeatN` bounded by `m`, else
  `refused`) or the selected region;
- `apply(d, ρ)`: the table's meaning of `d` for the preimage side
  `Side.preimage ρ side = fun j => side (ρ.apply j)`; the arguments and results are
  re-indexed, with no cast, because the preimage side's membership is the caller's
  by definition.

A local `loop` is `PIR.repeatN` over the iteration number, which starts at 0, and
the carried values, bounded by its maximum.

### Agreement and stops

A side with one role is that role's own execution. A side with several roles is
their joint execution, and it is one process only while its roles agree on every
control value they share.

- An adversary can give two honest roles different values: each `exchange` and each
  announcement of a `draw` from outside the side is a separate `receive`. Nothing
  in the meaning assumes a broadcast channel.
- At a `repeat` or a `branch`, the roles of the side that participate must hold
  equal copies. If they do not, the side stops with the reserved reason
  `incomplete`. At a `repeat` the copies are compared before the count is compared
  with the maximum: counts that differ stop `incomplete` even when one of them
  exceeds the maximum (control `counts_disagree_beyond_maximum`).
- A stop by any role of the side ends the side's process. Alone, the other roles
  of the side would go on until they needed something from the stopped role
  (controls `joint_side_stops` and `sender_alone_sends`).
- A statement about a side with several roles therefore shows two things: that
  `incomplete` is unreachable, and that a stop by one role leaves no other role of
  the side able to reach a decision. The second holds, for instance, when every
  role of the side but one performs no guard and no partial operation. Under both,
  the joint process restricted to any one of the side's roles is that role's own
  execution, with the other roles of the side as part of its environment.

The model has the rule and proves the first half of what such a statement needs in
two places. Participants are distinct, so for a side with one role, or with one
participant of a given `repeat` or `branch`, the agreement compares nothing:
`agreed_single` gives the copy of that participant. And `incomplete` has no other
source (see [Models, reasons and effects](#models-reasons-and-effects)). The
restriction of a joint process to one role is not defined in the model; it needs a
parallel composition of processes that matches the sends and receives at shared
sites.

### The proposition of an agreement

An honest execution starts with equal copies of an agreed value. A contract assumes
this of the inputs of the side it speaks of:

```lean
def Agreement.Holds (side : Side) (agreement : Agreement ports)
    (values : Values (SideValue model side) ports) : Prop :=
  ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
    ∀ (firstMember : side first.holder = true) (secondMember : side second.holder = true),
      Held.value (side first.holder) firstMember (values.get first.port) =
        Held.value (side second.holder) secondMember (values.get second.port)

def Agreements.InputsHold (side : Side) (agreements : Agreements inputs outputs)
    (values : Values (SideValue model side) inputs) : Prop :=
  ∀ agreement ∈ agreements.inputs, agreement.Holds model side values
```

`Program.agreements program` reads the agreements of a protocol from its header.
For Schnorr and both roles, `InputsHold` is `g = g' ∧ y = y'`
(`Schnorr.agreements_both`); for the verifier alone it holds of any inputs; the
completeness statement `Schnorr.honest_accepts` assumes it.

## Equations

`Zkc.IR.Core.Laws` gives what a proof needs to walk a body one operation at a time.

- **Root equations.** `Program.protocol_meaning` and `Program.function_meaning`
  open a program at its last definition: the meaning is the body's denotation over
  the table of the earlier definitions. `sideMeaning_step` turns an equation for
  the first operation of a region into one for the region: the operation's process
  bound to the rest of the region in the extended environment. Three forms give
  the result without a pending bind: `sideMeaning_step_done` (the operation returns
  without an effect), `sideMeaning_step_call` (one effect), and
  `sideMeaning_step_guarded` (continue or stop on a condition). `sideMeaning_ret`
  ends a region. `localMeaning_step`, `localMeaning_step_done`, `localMeaning_ret`
  and `localMeaning_stop` do the same for local regions.
- **Operation equations.** One per operation and membership case: `at_present`,
  `at_absent` and its forms `at_pure`, `at_partial`, `at_call`, `at_guard`;
  `exchange_internal`, `exchange_send`, `exchange_receive`, `exchange_outside`;
  `draw_owner`, `draw_outside`, `draw_received`, with `receiverReplies_present`,
  `receiverReplies_absent` and `receiverReplies_nil` for the receivers;
  `sample_owner`, `sample_outside`; `repeat_meaning`, `branch_meaning`;
  `apply_meaning`; and for local operations `localOperation_pure`,
  `localOperation_partial`, `localOperation_call`, `localOperation_conditional`,
  `localOperation_loop`, `localOperation_guard`. The left side is the operation
  applied to arbitrary arguments, so it matches whatever a body passes. The right
  side names the arguments' components by `get`, `tail` and `split`, which reduce
  on the literal lists of a body. An operation with regions is stated on the
  denotation of its literal regions and exposes each region's own denotation. Every
  side condition is a membership `side role = true` or `side role = false`; for a
  literal side, and for the preimage of one under a literal role map, it holds by
  evaluation (`rfl`).
- **Agreement.** `agreed_present`, `agreed_absent`, `agreeWith_present`,
  `agreeWith_absent`, `agreeWith_nil` and `agreed_nil` walk the participants one at
  a time, with the membership of each as the side condition. `repeat_agreed`,
  `repeat_disagree`, `branch_agreed` and `branch_disagree` state the result for
  equal and unequal copies at any positions; `agreed_single` for distinct
  participants of which one is in the side.
- **Table and entry equations**, generated by the importer: `name.d.table` says
  that the table of the program up to `d` is `d`'s meaning followed by the table
  before it, and `name.d.entry.c`, for every callee `c` that `d` calls or applies,
  that `c`'s entry in `d`'s table is `c`'s own meaning. After `at_call` or
  `apply_meaning`, rewriting with the entry equation names the callee's meaning.
  No proof unfolds the table.

```lean
theorem sideMeaning_step_call
    (step : protocolOperation model table side op (Operands.eval env arguments)
      (bodies.denote (sideMeaning model table side)) =
        .call effect fun reply => .done (results reply)) :
    (Region.letOp op arguments bodies next).denote (sideMeaning model table side) env =
      .call effect fun reply =>
        next.denote (sideMeaning model table side) (env.prepend (results reply))

theorem exchange_receive (senderAbsent : side sender = false) (receiverMember : side receiver = true) :
    protocolOperation model table side (.exchange sender receiver site type) arguments regions =
      .call (.receive ⟨headers.length, site⟩ type) fun reply =>
        .done (.cons (Held.of (side receiver) reply) .nil)

theorem sumcheck.round.entry.half_sums : ∀ (model : Model),
    (Program.table model sumcheck.fold_table).get (.there .here) =
      Program.meaning model sumcheck.half_sums
```

A step of a proof is `refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_`
followed by `congrArg (PIR.Process.call _) (funext fun reply => ?_)`. Each step is
a syntactic match of the equation's left side with the region at hand, so the
kernel never unfolds the denotation of a body: it evaluates memberships and, where
a statement names a value, the environment lookups of that value. The equations
were shaped by this: comparing an unfolded denotation with a folded one is the
comparison that costs the kernel minutes on a protocol of a dozen instructions.

For a symbolic side the transports stay in the equations. The statements that the
tests derive are at literal sides and at preimages of literal sides; a callee's
side meaning is stated for the preimage side at which the caller applies it.

## Importer

```lean
import_core <name> [stage "<stage>"] [with kernel_only, profile] from "<json>" [fixture "<path>"]
import_core <name> [stage "<stage>"] [with kernel_only, profile] from file "<path>"
```

The importer parses the package, selects the program of the stage (`original` by
default), and adds

| Declaration | Content |
|---|---|
| `name.catalogue : Catalogue` | the catalogue identities of the type rows and the operation rows |
| `name.operations : List OperationSignature` | the operation table |
| `name.row.«identity» : Var name.operations ⟨inputs, outputs, kind⟩` | per operation row, the variable of the row in the table |
| `name.d.definition : Definition …` | per package definition, the definition as a typed `Region` term |
| `name.d.wellFormed : name.d.definition.violation = none` | the kernel's decision of its residual conditions |
| `name.d : Program name.operations […]` | the program up to and including the definition |
| `name.d.table` | the table equation of the program |
| `name.d.entry.c` | the entry equation for every callee `c` of the definition |

The identity of a row is rendered as `name` or `name(static, …)`, a static as
`domain d`, `nat n` or `type T`, a nominal type as `constructor(static, …)` and a
structural type as `unit`, `bool`, `index`, `array[T]`, `tuple[T, …]` or
`variant[T, …]`: `schnorr.row.«curve.scale(domain curve)»`,
`sumcheck.row.«index.constant(nat 1)»`,
`schnorr.row.«law.uniform(type field(domain scalar))»`. Catalogue names use
letters, digits, `.`, `_`, `-` and `/`, a nominal type always carries parentheses,
and a type static names nominal types by their own identity, so the rendering is
injective and does not depend on row numbers. Two rows of one identity are refused.
A program names a row through its constant, and so do a model's laws: a statement
about `M.pure (.of schnorr.row.«curve.scale(domain curve)»)` keeps its text when a
package or a stage renumbers its table.

The importer infers the types of the values, builds each definition as an `Expr`
directly, with operands as unary `Var` terms whose implicit contexts are shared
subterms, and adds it with `addDecl`; there is no printing and re-elaboration. The
kernel type-checks the definition, then evaluates `Definition.violation` for
`wellFormed`. The recursion limit of each check grows with the size of what is
checked: the instructions of a definition, the rows of the table, the position of a
row. A refusal, by the importer or by the kernel, leaves the environment as it was.

The importer refuses malformed JSON, unknown formats and stages, dangling
references, a malformed static argument, catalogue name or names table, and the
constructs it does not interpret (oracle rows, oracle instructions and types,
`match`, computed oracle and relation definitions). It reports every typing
violation with a message, and every residual violation by evaluating the model's
own condition lists on the numbers of the package. `kernel_only` skips the checks
that the kernel also decides, so that the kernel refuses the term instead; the
importer then reports the kernel's cause: `typing`, with the kernel's account of
the ill-typed application, or `residual condition` with the name that the kernel
evaluates `Definition.violation` to. `fixture` compares the embedded package with a
JSON file as JSON values, at every elaboration of the importing module.

## What is checked and what is trusted

The kernel checks, for every imported definition:

- its typing, which includes the conditions of the first group of the
  [well-formedness](#well-formedness) table;
- its residual conditions, by evaluating `Definition.violation`;
- that a named row is a row of the operation table with the signature and kind of
  its type;
- every table equation and entry equation;
- every theorem about its meaning.

The importer decides, without a kernel check:

- **The reading of the JSON.** A theorem about `name.d` is a theorem about the term
  the importer built. That the term is the package's program is not a kernel fact.
- **The mapping of value numbers to variables.** A package names operands by value
  number; the importer turns each into a `Var` of the context. An operand that the
  importer mapped to another value of the same type and holder would type-check.
- **The choice of the stage.** The importer selects one program of the package by
  its stage name.
- **The other stages.** Their programs are read for their shape only. They are not
  type-checked, and no stage is recomputed from the previous one.
- **The association of rows with catalogue identities.** The name of a row constant
  and the entries of `name.catalogue` are the importer's reading of the type and
  operation tables. The kernel sees a row as a position and a signature; that
  row 1 of the Schnorr package is `curve.scale` over the domain `curve` is the
  importer's statement. A model's law names a row through its constant, so the law
  is about the operation that the package's table gives that identity.
- **Contracts, the proof declaration, stage parameters and the names table.** They
  are read for their shape; names choose the names of the declarations.

The importer's own typing and residual checks are a convenience: `kernel_only`
shows that the kernel refuses the same packages for the same cause.

The intended way to remove the trust in the value mapping is a kernel-checked
encoding of definitions: a function of the model from a `Definition` to the
positional form of the package, and, per imported definition, a generated equation
between that encoding and the literal read from the package. It is not implemented.

## Test packages

The fixtures in `lean/ir/fixtures/core/` are embedded in the test modules, which
compare them with the files. `schnorr.json` is the example of the package chapter.

| Package | Definitions | Exercises |
|---|---|---|
| Schnorr | 1 protocol, 2 roles, 11 instructions | sample, exchange, draw, local operations, agreements, laws on named rows |
| Sumcheck | 3 functions, 2 protocols | loops in functions, `call`, `apply` inside a two-participant `repeat`, a verifier guard and a draw per round, a final check |
| Opening | 1 protocol, 3 roles, 31 instructions | a setup role that samples a secret and sends a reference string and a key, commitment, draw, opening, pairing check |

The Sumcheck and opening sides, the Schnorr prover and the controls for a role map
that is not the identity, for the receivers of a draw, for the agreement statements
and for local regions are derived by walking the body with the equations. The
Schnorr sides and the small controls are also stated by unfolding the whole side.
The refusal tests check the cause of every refusal, by the importer and, with
`kernel_only`, by the kernel, and that a refused command adds no declaration.

## Scale

Operands, rows and callees are unary `Var` terms, and the lists they are typed over
are written out in the terms. Importing is linear in the instructions of a
definition when operands are recent values, and quadratic in the distance of an
operand, in the number of operation rows, and in the number of definitions. A
positional representation of variables and named header lists would remove the
quadratic terms; neither is implemented.

## Not implemented

Oracle types, rows and operations, `match` and the injections into variants,
computed oracle and relation definitions, contracts and claims, the stage tables and
the stages other than reading their programs are specified and not formalized. The
kernel-checked encoding of definitions is not implemented. A generic statement that
a side with agreeing roles restricts to each role's own process with the others as
environment needs a parallel composition of processes that matches the sends and
receives at shared sites; it is not provided.
