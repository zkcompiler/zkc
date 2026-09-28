# Mathematical subject and placement witness format

This is the version-1 interchange contract for the
[mathematical profile](../spec/profiles/source/mathematical-protocols.md).
The [reference codec and vectors](../../tests/fixtures/mathematical/README.md)
exercise byte canonicality. Typed readers and placement checking have separate
[implementation status](../status.md#mathematical-protocol-foundation).

## Canonical values and digest

Transport JSON permits Boolean, unsigned 64-bit integer, Unicode scalar string,
array and object. Null, floats, negative integers, duplicate keys and unpaired
surrogates are refused. No Unicode normalization occurs. Object keys compare
by UTF-8 bytes. Convert each value to a logical tree:

| Value | Logical tree |
|---|---|
| Boolean | `["boolean", "false"]` or `["boolean", "true"]` |
| Integer | `["natural", canonical decimal string]` |
| String | `["string", exact string]` |
| Array | `["array", converted element, ...]` |
| Object | `["object", key, converted value, ...]`, strictly increasing keys |

Decimals are `0` or a nonzero ASCII digit followed by ASCII digits. Binary
`natural` payloads have the same u64 bound as JSON integers. The
[existing logical encoding](artifact-format.md#canonical-logical-encoding)
encodes strings with tag byte 0, u64 little-endian UTF-8 length, then bytes;
arrays with tag byte 1, u64 little-endian count, then children. Converted trees
have at most 16 MiB, 200,000 nodes, 32,768 children per array and depth 64
(root depth zero). Thus a value array has at most 32,767 elements and an object
16,383 fields. Each container adds one tree depth; scalar payload adds one.
A nested repeat adds three levels from body through steps/step/nested body, so
the exact depth check includes enclosing module records and static expressions.
Flat sequential steps do not consume one depth level per statement.

Decoders consume the whole input and refuse noncanonical order, duplicates,
unknown tags, invalid decimals, truncation and trailing bytes. Binary decoders
check byte/node/depth/count limits before recursive allocation. Encoders charge
these budgets while traversing, before constructing an intermediate full tree.
The Python JSON entry point separately caps transport text at 1 MiB before
parsing; whitespace can affect that safeguard, but never the subject digest or
binary admission. JSON and binary resource admission are distinct interfaces.
The independent Lean capture reader accepts at most 16 MiB of JSON text and
checks the same canonical codec limits. It retains object keys until duplicate
checking and bounds decimal tokens before numeric conversion. The development
runtime host retains its smaller 1 MiB input ceiling.

The subject digest is SHA-256 of ASCII `zkc.math.subject.v1`, a zero byte,
then these canonical bytes of `{profile:"zkc.math.v1", manifest, module}`.
Debug spans and presentation names are outside this record. Role names are
semantic external role identities and remain inside. A semantic site also
remains inside. Digests identify captured artifacts; checking takes actual
admitted terms and their interpretations.

## Declarations and scopes

The native closed installation adapter reads totality from the common logical
declarations. Only positively classified operations can be installed as pure;
unknown identities and known Ordered contracts are refused. Its current subset
has one result, no natural parameters or attributes, and closed unary nominal
value types plus Fin 2 (the common bool type). Exact common binding resolution
checks associated domains, including a group's scalar field. Wire payloads use
the existing nominal codec catalog. Nullary entropy services resolve existing
sampling contracts with one RNG input, one reply and one RNG successor. The
service descriptor retains the exact field or nonzero-field reply domain; it
does not establish a distribution or native-provider adequacy theorem. Root
parameter aliases remain explicit in admitted instances. Physical implementations
are selected later.

The adapter derives package pins from canonical descriptor bytes under
the prefix `zkc.math.installation.v1` followed by a zero byte. These descriptors
identify the resolved logical binding or codec payload and the adapter version.
They are not implementation hashes. The selected registry still checks every
signature and type; independent interpretations supply their own meanings.

Records have exactly the following fields. Lists preserve order unless stated
otherwise. References and arities are unsigned integers. Unknown fields and
tags are refused. The generic byte codec does not validate this typed schema.

```text
manifest = {domains:[identity], operations:[identity], wires:[identity],
            services:[identity], laws:[identity]}
identity = {name:string, version:string, digest:string}
module = {roles:[string], types:[typeTemplate], operations:[operation],
          wires:[wire], capabilityTypes:[capabilityType], roots:[root],
          relations:[relation], definitions:[definition], entry:entry}
typeTemplate = {statics:uint64, body:type}
typeUse = {type:typeRef, statics:[static]}
type = ["nominal", domainRef, string, [static]]
     | ["product", [typeUse]] | ["fin", static] | ["vector", typeUse, static]
     | ["polynomial", domainRef, staticArity, staticDegree, "individual"|"total"]
     | ["residual", domainRef, staticArity, staticDegree]
static = ["literal", uint64] | ["parameter", uint64]
       | ["add", static, static] | ["multiply", static, static] | ["pow2", static]
capabilityType = {identity:serviceRef, statics:uint64,
                  arguments:[typeUse], result:typeUse}
capabilityUse = {type:capabilityTypeRef, statics:[static]}
capabilityParam = {signature:capabilityUse, roles:[role]}
root = {signature:capabilityUse, roles:[moduleRole]}
operation = {identity:operationIdentityRef, statics:uint64,
             capabilities:[capabilityUse], arguments:[typeUse], result:typeUse,
             purity:"total"|"ordered", distinct:[[uint64,uint64]]}
wire = {identity:wireIdentityRef, statics:uint64, type:typeUse}
port = {roles:[role], type:typeUse}
relation = {statics:uint64, public:[typeUse], witness:[typeUse],
            assumptions:[lawRef], body:region}
definition = {statics:uint64, roles:uint64, capabilities:[capabilityParam],
              arguments:[port], results:[port], relations:[relationBinding], body:body}
relationBinding = {relation:relationRef, statics:[static],
                   public:[valueRef], witness:[valueRef]}
entry = {definition:definitionRef, statics:[uint64], roles:[moduleRole],
         capabilities:[rootRef]}
```

Manifest digests are exactly 64 lower-case hexadecimal characters and cover the
registered interpretation/contract package named by `(name,version)`. Admission
resolves the actual package and its prerequisites; a digest never supplies a
law. Duplicate `(name,version)` pairs within a manifest table are refused.
Imports are flattened into resolved declarations in v1; no unused dependency
field claims import correspondence. Duplicate module role identities are
refused. Role sets are strictly ascending and duplicate-free.

Every static parameter scope is local to its declaration and has the declared
arity. A `typeUse` explicitly substitutes arguments from its user's scope into
an earlier type template. Nested type uses refer only to earlier templates;
exact duplicate templates are refused. Substituted types need no extra table
entry. Equality expands templates and uses the profile's checked static equality.
The v1 admission envelope limits each expanded mathematical type to 65,536
constructors and structural depth 64, with root depth zero. Nominal,
polynomial, residual and finite-index types count as one constructor. A product
counts one plus the sum of its children, counting repeated references each
time; an empty product counts one. A vector counts one plus its element type,
independently of the vector length. These limits apply to declared and derived
types, including unused declarations and unused node results. Shared storage
does not reduce the expanded count. Type-template traversal, syntax nesting,
leaf payloads and total admission work have separate limits. Template traversal
counts a referenced constructor at the current depth and advances once for
each product/vector child; it refuses beyond depth 64 before expansion.
Cached instances still obey the complete structural bound. Native traversal
and structural-depth refusals use `math-type-template-depth` and
`math-type-depth`, respectively. Both report the same depth-capacity violation
at different checking phases; cache state can change which detects it first.
Expanded node overflow uses `math-type-size`. A resource refusal
does not establish that two mathematical types are unequal.

Operations, wires, relations and capability types each have their own scope.
Declared `purity` and `distinct` must equal the resolved registry contract.
The registry also checks the complete signature: static arity and ordering,
capability uses, argument and result types, and attribute schema. Mathematical
registry declarations are natural-parametric over fixed domain identities;
an adapter must explicitly specialize any existing Domain/Type parameters.
The same requirement applies to service signatures, wire payload types and
nominal type families. Polynomial and residual domains must be registered fields.
Operation capability uses and argument/result uses share its static scope.
Definition ports and capability parameters share its scope. Source roots are closed and normalized: every static argument is exactly
`["literal",n]`; parameter references and arithmetic expressions are refused there. Entry statics are closed
numerals. Input values are supplied separately in the admitted entry binding.

Definitions declare local role parameters `0 .. roles-1`. Entry and invoke role
bindings are injective ordered lists of exactly the callee's arity. Capability
bindings are ordered lists and may repeat: ports are names, resolved roots are
identities. Capability signature equality compares the resolved service identity,
normalized static arguments and expanded argument/result types. A duplicate
capability-type declaration does not create a new service or root identity.
Types must match after substitution; each mapped callee permission
set must be a subset of the caller port's permission set. Root resolution
composes entry bindings with all invoke bindings on the dynamic path. Distinct
root ordinals mean separate state components, without implying random
independence. Operations must define behavior under aliasing except for pairs
in their registered `distinct` requirement, which admission discharges on every
syntactically reachable instance, including calls inside zero-count repeats.
Unused templates retain their requirements without discharging them. `distinct`
lists strictly increasing pairs in lexicographic
order; pure operations have no capabilities or such requirements. Fresh setup
is not encoded in v1; future allocated roots need explicit site/path identity.

Templates are formed symbolically, with every body checked even for a zero
count. The execution/placement input in v1 is the closure reachable from the
closed entry. Static evaluation, substitution and instance expansion have
explicit work budgets; overflow beyond u64 or exhausted checking work refuses
admission. No symbolic-family theorem follows from successful instantiation.

## Bodies and pure regions

```text
region = {captures:[valueRef], nodes:[node], outputs:[regionRef]}
node = ["operation", operationRef, [static], attributes, [regionRef]]
     | ["tuple", [regionRef]]
     | ["project", regionRef, uint64]
     | ["map", static, region]
     | ["fold", static, [regionRef], region]
body = {steps:[step], terminal:terminal}
terminal = ["return", [valueRef]]
         | ["stop", site, role, stopReason]
step = ["pure", region]
     | ["local", site, role, operationRef, [static], attributes,
        [capabilityPortRef], [valueRef]]
     | ["query", site, role, capabilityPortRef, [valueRef]]
     | ["guard", site, role, valueRef]
     | ["message", site, wireRef, [static], sender, receiver, valueRef]
     | ["invoke", site, definitionRef, [static], [role],
        [capabilityPortRef], [valueRef]]
     | ["repeat", site, static, [port], [valueRef], [valueRef], body]
stopReason = "reject"|"abort"|"exhausted"|"incomplete"|"refused"
```

`attributes` has the exact schema owned by the resolved operation; its meaning
belongs to that interpretation. Pure nodes require registered total purity.
Local steps require ordered operations, complete capability bindings and owner
permission. Query uses its capability's actual argument/result signature.
Guard consumes an owner-available condition and stops with `reject` when false.
A message selects the wire instantiated by its static arguments; sender and
receiver differ. Calls name only earlier stored definitions. Dynamic effectful
branches, runtime-derived counts and setup allocation are refused by v1.
Public counts must be resolved into the closed entry before this interface.
The v1 condition type for guards and relation results is `Fin 2`, with `1`
meaning true and `0` false. This fixes the concrete serialized language's
condition interpretation; the independent abstract Lean core remains parametric.

Primitive operation/query results are single mathematical values; products are
explicit types. Regions and protocol calls have ordered multiple outputs.
This matches the minimal Lean core and gives one packing convention rather
than implicitly flattening every product. Tuple and projection nodes have built-in total meanings: ordered product
construction and selection of one component. The empty tuple constructs the
empty product. These fix the meaning of witness packing paths independently
of any registered domain operation. No projection is implicit in a value
reference.

Value references index the lexical context, zero-based, with the newest ordered
result block prepended. Definition arguments form the initial block. Pure
outputs, local/query results, messages and call outputs prepend their declared
order. Each pure node prepends its own ordered results. No forward or implicit
outer reference is allowed. A pure-step region's captures reference its enclosing body context; map/fold
captures reference the enclosing pure-node context; relation captures reference
the public-then-witness context. In each case
its nodes see only the region parameters and earlier node results.

Region parameter blocks are:

- Pure region: captures.
- Map body: public `Fin count` index, then captures.
- Fold body: public index, initial accumulator block, then captures.
- Repeat body: public index, declared carried ports, then captures.

Map returns one `Vector T count` for each body output of type `T`. Fold yields
exactly the initial accumulator types and availability after every iteration;
its outer outputs have those types. Repeat declares its invariant carried ports
explicitly, so initial operands may have wider availability. The two operand
lists after those ports are initial values and captures. Body results must
cover the declared carried ports. Only the final carried block is prepended
to the outer context; count zero returns the initial block. Pure node
availability follows the profile's intersection rule, including the index.
Captures alone do not create dependencies on unused values.

Fold visits indices in ascending order, threading the accumulator as a left
fold. Its exact availability invariant rejects both narrower and wider body
outputs. In particular, a public initial accumulator cannot become private by
reading a private capture. Repeat provides explicit carried ports when a
narrower invariant is required. A repeat body may stop instead of returning;
its complete syntax is still checked when its count is zero.

Empty availability is allowed: such a value supplies no role component. A
definition's participating roles are its own role parameters, mapped to module
roles by the closed instance. Entry bindings may omit module roles; omitted
roles do not gain source components from nullary nodes or public indices.

A relation has one context block of public ports followed by witness ports, represented
as mathematical types at one abstract evaluator role. Its region captures that
context explicitly and returns one condition. A relation binding selects only
definition arguments, with matching substituted types; theorem use must supply
components at a role that has all selected inputs and the declared assumptions.
Declaring the relation does not widen availability or make its predicate true.

Effect/control sites (including guard, repeat and stop) are dense preorder
ordinals within a definition; pure nodes have no effect site. Dynamic origins
append invocation `(site)` and iteration `(site,index)` frames. Site numbering
is checked independently of binder references and root identity.

## Located target

Placement targets the existing admitted `source::Module`, encoded as
`zkc.protocol/1` by the [common carrier](interactive-execution.md). It uses
inline `pure`, closed `root` declarations, ordered `query`, `guard`, messages,
and the existing instance and entry declarations. There is no separate
`zkc.math.located.v1` grammar or copied mathematical declaration registry.
The mathematical input, its manifest and relation bindings remain in captured
source custody. The target is independently admitted from its actual contents.

Each closed source instance maps to one parameterless target protocol and one
instance. Local source roles resolve to actual module-role names; target
instance role assignments are identities. Root parameter aliases resolve to
closed source root identities before placement. The complete source root table
maps injectively to target root names; projection retains that table. Operation
and service bindings resolve through the installed common logical contracts.
The witness checks their actual applications against the mathematical packages;
names and hashes alone do not establish this correspondence.

The target digest is SHA-256 of ASCII `zkc.math.placement.target.v1`, a zero
byte, then the existing canonical logical encoding of the actual common carrier
array. It includes target names as custody data. Binding names do not acquire
semantic significance merely because they occur in a digest.

The initial executable placement profile has one closed instance, nominal
field/group/nonzero-field values and Boolean values, attribute-free total
operation graphs, messages, nullary entropy queries, guards and return/stop.
The entry role map covers every module role. Operations and wires have no
natural parameters in this installation. Placement re-admits the retained raw
subject against that concrete installation, including unused manifest entries.
The profile uses the common carrier's implicit default codec for each payload
type. Placement resolves the full pinned wire identity through the same
installation as operations and services. Agreement between that installed codec
and the runtime codec remains an external native realization premise; the target
carrier does not encode an explicit codec identity on each message.
It explicitly refuses unsupported products, map/fold, ordered local operations,
invokes, repeats and relation bindings. Those constructs remain in the
mathematical language and later foundation requirements. No unsupported
constructor is silently erased or recoded as an unrelated legacy construct.
In particular, mathematical relations are not R1CS/AIR source declarations.
A future relation adapter must check their actual public/witness input mapping.
Implementation coverage belongs in [status](../status.md#mathematical-protocol-foundation).

## Placement witness

```text
witness = {profile:"zkc.math.placement.v1", source:digest, target:digest,
           instances:[instance], roots:[rootMap], operations:[operationMap],
           wires:[wireMap], components:[component], sites:[siteMap],
           results:[result]}
instance = {sourceDefinition:uint64, targetProtocol:string, targetInstance:string,
            statics:[uint64], roles:[uint64], capabilities:[uint64]}
rootMap = {source:uint64, target:string}
operationMap = {source:uint64, target:string}
wireMap = {source:uint64, schema:string}
sourceAddress = {definition:uint64, regions:[uint64], binding:uint64}
placedValue = {regions:[uint64], name:string, path:[uint64]}
component = {instance:uint64, source:sourceAddress, role:uint64,
             target:placedValue}
siteMap = {instance:uint64, site:uint64, targetSite:string,
           kind:"message"|"invoke"|"repeat"|"guard"|"stop"|"local"|"query",
           callee:[uint64]}
result = {instance:uint64, role:uint64, sourcePort:uint64,
          targetPort:uint64, path:[uint64]}
```

A witness role is a module-role ordinal obtained by applying the closed
instance's role binding. Source root ordinals likewise name actual closed
roots, including aliases in `capabilities`. Instance zero is the entry.
Instances are independently discovered depth-first in source site order,
including dormant bodies. Equal definition/static/role/root tuples reuse the
first instance. The witness cannot choose a different closure. Target protocol
and instance names are bijective with that closure; extra declarations are
refused. Each invoke's `callee` is its exact composed instance reference; other
site kinds have no callee. The initial profile refuses invokes and repeats.

Source addresses retain the mathematical format's scoped binding ordinals.
`regions` is an even sequence of `(statementOrdinal, childOrdinal)` pairs;
child zero enters a pure/repeat region, and `(nodeOrdinal,0)` enters map/fold.
Parameters precede result bindings in each region. Every demanded scoped binding has its own component record, including region
parameters, node results, and outer pure-step outputs. Captures and yields check
their actual alias edges. A yielded capture or repeated yield remains explicit;
there is no alias exemption or synthetic identity operation.

Target value addresses are resolved in the actual mapped protocol. Their
`regions` traverse actual Source instruction positions and child regions;
`name` selects an SSA binding in that scope. An empty path names a whole value.
A nonempty path selects a product subtree and requires matching typed projection
in the target; the initial profile accepts only empty paths. Target site names
are actual Source site strings, not reconstructed dense numeric ordinals.
Mathematical dense preorder sites remain a source formation invariant.

### Independently computed demand

The checker derives the required `(source address, module role)` domain from
actual source terms. The witness cannot nominate live values or omit effects.
The domain contains:

- Every argument-interface component at each role in that argument's availability.
- Every ordered-result component and every declared result component at its role.
- Every effect operand at the role that performs that effect, including sent
  values, guard conditions, ordered local inputs and supported call boundaries.
- The backward closure of those components through total graph operations and
  explicit region captures, for the same role.

A message result is available at exactly its sender and receiver; both ordered
components are in the domain even if subsequently unused. The sender aliases
the sent operand; the receiver names the actual message output.

Only unobserved total computation can be omitted. A demanded pure output demands
its defining operation and operands; unused captures do not reduce the
availability of an independent node. Message demand follows two different
rules: the sender component aliases the existing sent operand, while the
receiver component is the fresh received value. The receiver's component never
induces demand for an honest sender expression. Query results remain results of
their specific occurrence and root, even when supplied replies happen to agree.

Components cover exactly this computed domain. Each component resolves to the
actual output of its defining target construct or argument port; matching only
its name, type and owner is insufficient. Each target pure node must implement the mapped demanded source
node at that role using its actual mapped operands. This placement boundary does
not accept additional algebra rewrites; later checked optimization can do so
under its own laws. Target pure regions introduce no arbitrary local-service
reply. Pure algebra stays inspectable through participant projection. At each source
pure step, the target emits one region for each role demanding an output, in
ascending module-role order at that step position. Demanded nodes, captures and
outputs retain source order; duplicate captures may share the same actual
enclosing SSA name, and duplicate yields remain separate output ports. A
pass-through region contains a yield without introducing an identity operation.

### Interface and effect coverage

Argument components partition the target argument ports by role and source
order. Result records similarly cover the target result ports, in source port
order within each role. More general product packing requires every target leaf
exactly once, including empty products; a source result must occupy one subtree
of its exact type. The initial profile uses whole scalar/group/Boolean ports.
Results remain declared and mapped in stop-terminated bodies. Target result
ports are grouped by ascending module role, then source port; `targetPort` is
the port index within that role. Every actual operand and result type is checked against the installed logical
view of its source type; a spelling alone is not a type proof.

Each source effect site has exactly one mapped target effect with the same
owner(s), root or wire, operands and outcome shape. Their actual instruction-position order is preserved, so two queries on the
same root cannot be swapped merely by permuting witness entries.
The mapped sites partition all target effect sites; additional, missing or
merged target effects refuse. Pure region wrapper sites are structural labels
and do not count as mathematical effects. Original ordered local operations
cannot be hidden inside those wrappers. A guard remains reject-on-false at its
own mapped site, independently of later native realization.

Root mappings biject the entire source and target root tables in table order. Target root
service applications, result domains and permitted owners agree with the actual
source capability signatures and installed service packages. Distinct source
roots cannot alias one target root. Operation mappings cover exactly the source
operations demanded by the placed graph; wire mappings cover the used wire
declarations. The checker validates actual target bindings and message payload
types, and refuses extra executable bindings or functions in this initial slice.
Each demanded source operation declaration gets its own target binding; service
bindings are shared exactly by source manifest service index and include those
needed by unused roots. These bindings together cover all target bindings. Each
used source wire declaration gets its own schema. Unused mathematical
declarations remain in source custody. Restated instance, definition and site
fields are checked against their actual source values.

Components sort by `(instance,source.regions,source.binding,role)`, sites by
`(instance,site)`, and results by `(instance,role,sourcePort)`. Root, operation and
wire maps sort by source index. Keys are unique. Numeric array ordering is
lexicographic with shorter prefixes first. All record keys and arities are
exact. The canonical codec's byte/node/depth bounds apply to witnesses, and
exhaustion refuses the entire check.

Placement witnesses cover the inline located checkpoint. Physical pure
outlining and root state threading are subsequent transformations with their own
checked actual-body and interface maps. Their relations preserve distinct
obligations: total pure-call folding, ordered service realization, and physical
resource adequacy. An introduced sampler call cannot be erased by pure-call
folding. The [placement law](../spec/profiles/compiler/mathematical-placement.md)
compares independently defined meanings of the retained mathematical input and
actual located target; custody digests discharge none of its premises.
