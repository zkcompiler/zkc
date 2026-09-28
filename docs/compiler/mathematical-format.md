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

Decimals are `0` or a nonzero ASCII digit followed by ASCII digits. The
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

The subject digest is SHA-256 of ASCII `zkc.math.subject.v1`, a zero byte,
then these canonical bytes of `{profile:"zkc.math.v1", manifest, module}`.
Debug spans and presentation names are outside this record. Role names are
semantic external role identities and remain inside. A semantic site also
remains inside. Digests identify captured artifacts; checking takes actual
admitted terms and their interpretations.

## Declarations and scopes

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
Operations, wires, relations and capability types each have their own scope.
Declared `purity` and `distinct` must equal the resolved registry contract.
Operation capability uses and argument/result uses share its static scope.
Definition ports and capability parameters share its scope. Source roots are closed and normalized: every static argument is exactly
`["literal",n]`; parameter references and arithmetic expressions are refused there. Entry statics are closed
numerals. Input values are supplied separately in the admitted entry binding.

Definitions declare local role parameters `0 .. roles-1`. Entry and invoke role
bindings are injective ordered lists of exactly the callee's arity. Capability
bindings are ordered lists and may repeat: ports are names, resolved roots are
identities. Types must match after substitution; each mapped callee permission
set must be a subset of the caller port's permission set. Root resolution
composes entry bindings with all invoke bindings on the dynamic path. Distinct
root ordinals mean separate state components, without implying random
independence. Operations must define behavior under aliasing except for pairs
in their registered `distinct` requirement, which admission discharges on every
reachable instance. `distinct` lists strictly increasing pairs in lexicographic
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

A relation has the context public ports followed by witness ports, represented
as mathematical types at one abstract evaluator role. Its region captures that
context explicitly and returns one condition. A relation binding selects only
definition arguments, with matching substituted types; theorem use must supply
components at a role that has all selected inputs and the declared assumptions.
Declaring the relation does not widen availability or make its predicate true.

Effect/control sites (including guard, repeat and stop) are dense preorder
ordinals within a definition; pure nodes have no effect site. Dynamic origins
append invocation `(site)` and iteration `(site,index)` frames. Site numbering
is checked independently of binder references and root identity.

## Located subject

A placed subject has exactly `{profile:"zkc.math.located.v1", manifest, module}`.
Its digest uses ASCII `zkc.math.located.v1`, a zero byte, then the same canonical
codec. It is a new finite encoding of the extended located carrier; the old
common-protocol JSON does not implicitly acquire this format.

The located module copies `manifest`, `roles`, `types`, `operations`, `wires`,
`capabilityTypes`, `roots` and `relations` verbatim; the checker verifies equality.
Only `definitions` and `entry` change, and the located module additionally has
`pureLocals`. Thus role and root ordinals have one shared numbering space, and
all declaration templates retain their scopes.
Definitions have `statics:0`, `roles:module.roles.length`, no capability
parameters and the same port/body record syntax. All uses in definition bodies
are closed, and every port has exactly one role. Closed static expressions
are canonical `["literal",n]`, including source roots. Type-template bodies
remain generic as declared. Roots are the module's explicit
closed service instances. Local/query capability references name those roots.
Calls have empty static/capability lists and the literal identity role list
`[0,...,module.roles.length-1]`; the reference equals the selected callee
instance's target definition. The entry has those same empty lists and role
list, with `definition = instances[0].targetDefinition`. Referenced definitions
have already been instantiated. Located relation operands are `{argument:uint64,path:[uint64]}`, selecting
argument product subtrees. Bindings replicate exactly at each role where all
selected source inputs are available, ordered by source binding index then
role. Each is instantiated through the checked argument map. A zero-operand binding
is replicated once per role; its ordered position determines that role.

Located pure regions contain only single-role values. Nullary pure nodes use
the enclosing region owner, so a placed pure step is `["pure", owner, region]`.
Its inline meaning is the registered pure evaluation without an external reply.
Located messages use the same message syntax, but bind only a receiver-owned
value: the sender keeps the old operand. Repeat supplies **one index port per
module role**, in role order, before carried ports and captures. This replaces
the shared source index while retaining one common iteration frame. Remaining
steps use the syntax above. Definitions/regions remain flat; typed folding into
the existing continuation representation is a separate correspondence.

Inline placement introduces no local service to evaluate pure operations.
An outlined candidate uses `["outlined", site, owner, localDefinitionRef,
[valueRef]]` and adds a `pureLocals` array to its module. Each local definition
is `{arguments:[typeUse], results:[typeUse], body:region}` with no static scope
and captures into its argument context. Inline subjects have `pureLocals:[]`
as well. These actual closed bodies and their result packing are checked before
folding introduced calls; an arbitrary local service remains arbitrary.

## Placement witness

```text
witness = {profile:"zkc.math.placement.v1", source:digest, target:digest,
           instances:[instance],
           components:[component], sites:[siteMap], results:[result],
           introducedPureCalls:[outlined]}
instance = {sourceDefinition:uint64, targetDefinition:uint64,
            statics:[uint64], roles:[uint64], capabilities:[uint64]}
address = {definition:uint64, regions:[uint64], binding:uint64}
regionAddress = {definition:uint64, regions:[uint64]}
placedValue = {address:address, path:[uint64]}
component = {instance:uint64, source:address, role:uint64, target:placedValue}
siteMap = {instance:uint64, site:uint64, targetSite:uint64,
           kind:"message"|"invoke"|"repeat"|"guard"|"stop"|"local"|"query",
           callee:[uint64]}
result = {instance:uint64, role:uint64, sourcePort:uint64,
          targetPort:uint64, path:[uint64]}
outlined = {instance:uint64, sourceRegion:regionAddress, role:uint64,
            targetSite:uint64, localDefinition:uint64,
            arguments:[placedValue]}
```

All witness role and root indices use the shared module numbering. A source
`component.role` or `result.role` names the **module role** obtained by applying
its instance's role binding to the source definition's local role. Instance
zero is the entry. Instances are discovered depth-first, visiting calls in site
order, including calls syntactically inside zero-count loops. Equal (source
definition, closed statics, module roles, roots) tuples reuse the earliest
instance. Instance records and target definitions are in bijection.
`capabilities` contains resolved root indices in source parameter order. Each
call site's `callee` is a singleton instance reference with exactly the composed
static/role/root binding; every other kind has an empty list. Unreachable extra
instances and target definitions are refused. Target definition order must also
satisfy earlier-callee formation; it need not equal instance order.

`regions` is an even sequence of `(statementOrdinal,childOrdinal)` pairs from
a definition body. Child zero is a pure/repeat body; inside a pure region the
pair is `(nodeOrdinal,0)` for map/fold. Calls reference stored definitions, not
child regions. Target addresses follow the same rule over flat target bodies.
`binding` counts region parameters, then all result blocks in source order.
Terminal nodes bind nothing. Outer outputs of a **pure-step region** are the canonical addresses for its
output values. A node selected as such an output may also have an internal
address; a component entry for that internal alias is omitted. This exclusion
does not apply to map/fold body outputs, whose values differ from their outer
vector/accumulator results. Multiple outer outputs aliasing the
same node have equal mapped values.
A `path` means repeated built-in `project` on a product-typed value; an empty
path selects the whole value. Every projection is type checked.

The component map covers exactly every source binding/available-role pair,
except pairs `(address,r)` strictly inside a region outlined at that same
module role `r` of the same instance, and the pure-step internal output aliases described above.
Inlining one role while outlining another does not remove the inlined role's
internal entries. No liveness exemption changes this v1 domain. The
located graph may retain unused pure bindings; demand analysis and later checked
rewrites can eliminate their execution without making witness coverage ambiguous.
For an outlined region, outer output component entries give the actual outlined
call result subtrees. Original source effects always remain represented.

For a message, the sender entry equals the sent operand's entry; the receiver
entry is the fresh result of the mapped message. Other source values may alias
that result only through subsequent explicit source references/computation.
A received value cannot be replaced by an honest sender expression.

A product leaf is a non-product type or an empty product. For each role, mapped
source result subtrees partition every target result port's leaves exactly once.
Each source result occupies a single subtree of the same type; splitting it
across target ports is refused. Port indices use the complete result lists,
before filtering by role. The argument block's component entries obey the same
coverage rule for target argument ports. Entry inputs use instance zero's
argument map. At every invoke, each target operand subtree equals the caller's
component of the corresponding source operand; caller invoke-result components
use the callee instance's result map and the actual target invoke result block.
These obligations also apply to carried values across repeat initial/yield edges.

For each instance, site entries are total on source sites and injective into
target sites. Their image and the introduced outlined-call sites are disjoint
and partition the target definition's dense site ordinals. Extra, duplicated or
missing target effects are refused.

Components sort by `(instance,source.regions,source.binding,role)`; sites by
`(instance,site)`; results by `(instance,role,sourcePort)`; outlined entries by
`(instance,sourceRegion.regions,role)`. Numeric
lexicographic ordering compares arrays elementwise, shorter prefix first.
Keys are unique, so each map is a function. Addresses' definition fields must
match their instance's source or target definition as appropriate.

Placement preserves calls and repeats one-to-one: it does not unroll, fuse,
peel or inline them. Dynamic paths map frame by frame using the site/instance
maps; only checked introduced pure-call frames may be erased by outlining.
An outlined source region must be the body of a pure step; nested map/fold
bodies are not separately outlined in v1. Inline witnesses have no introduced calls. Outlined arguments contain exactly
one entry for each source capture available at that module role, in capture
order. Every entry has an empty path and its address equals the actual target
operand's address. That value must equal the corresponding capture component;
if its component map uses a product path, the operand must be the result of the
matching explicit projection chain. Local argument `j` receives target operand
`j`. Capture positions, including duplicate values, determine correspondence. Its actual output arity/types and
packing must match the region's outer component entries, in output order. The [placement law](../spec/profiles/compiler/mathematical-placement.md)
checks the common interpretation tables and maps dynamic site identities.
Digest fields are 64 lower-case hexadecimal characters. The canonical codec's
same byte/node/depth limits govern witnesses: large component maps can exhaust
the node budget before their array limit. Exhaustion refuses the whole check;
partial witness coverage is never accepted. Custody hashes alone discharge none of this.
