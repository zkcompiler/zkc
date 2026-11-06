# Written source AST

`zkc-compile language-check --source-ast` adds a `source_ast` member containing
`zkc.source-ast/0`. The corresponding C++ API is `inspectWrittenSource`.
The artifact retains written syntax for the independently checked source
correspondence connection. It neither admits an IR nor certifies elaboration.

The parser is a named trust boundary. `capture` binds captured modules and
assets; `installation` binds the installed declaration rows. Installed
declarations are catalog rows, not written syntax: the artifact contains
captured sources only. Each source record contains its logical module, origin,
UTF-8 byte length and SHA-256. Diagnostic filesystem paths are excluded. All
captured declarations are present, including private ones. This artifact has different consumers from the public
API inspection graph, whose representation-privacy policy still applies there.

## Shared contract and producer boundary

The frontend owns this source contract: its node vocabulary, written fields,
source identities and diagnostic spans. Compiler and formal consumers refer to
these records, not to a particular parser's classes, enum ordinals or allocation
order. The current parser implements the producer through `inspectWrittenSource`;
replacing that parser does not require a second source format or a compatibility
reader. New language forms extend the owned contract and its consumers together.
Grammar-neutral does not mean erasing written syntax: omission, binding structure,
ordering and notation remain explicit even when several concrete spellings map
to the same node.

The identity domains are distinct:

| Reference | Scope and meaning |
| --- | --- |
| `{owner,path}` | A written node within the exact `capture` and `installation`; neither a standalone global identity nor an executable event address |
| `{module,begin,end}` | A UTF-8 range in the source record bound by that capture; several nodes may share it |
| A closed declaration symbol | A checked instance, with its template and substitution supplied by the instance export; its printed name is not a derivation |
| A structured `row` | An array position within the exact admitted `snapshot`, bound by `admission`; neither an AST path nor a persistent event label |
| An authored site or claim label | Source content retained in its node; resolution to an admitted occurrence or request is a separate checked elaboration step |

An AST path can survive a binder rename while the capture identity changes.
It cannot carry a claim, realization selection or proof receipt into a different
capture. Inserting a statement may change paths without renaming an authored
event label. A consumer must not use an exact-span match, a positional path or
a generated symbol as evidence that those two occurrences agree.

Binding observations, candidate lists and source-to-row associations below are
search proposals. The selected callee, owner, role, typed specification term or
law in the admitted program remains meaning-determining contract content.
Discarding an association can leave a correspondence obligation open; it cannot
remove that content from the admitted subject or establish the missing link.
A new parser can produce the same contract without importing this implementation's
private syntax records. An independent checker still checks its supported
fragment against the retained admitted program.

## Retention boundary

Headers are copied before declaration collection, import resolution, generated
Entry members, inferred requirements or signature inference. Bodies are parsed
after imported notation syntax is available, then frozen before name resolution,
operator elaboration, owner inference and scoped extraction. The frozen records
are owned by the immutable checked project. Inspection never reconstructs
written syntax from final types, generated symbols or optimized instructions.

A relation's implicit Boolean result is absent. Inline relations occur at their
clause path, without synthetic `clause_…` declarations or inherited arguments.
A construction handler with several occurrence selectors has one written body
and an ordered selector list. External module links remain nodes of their
containing module, separate from the linked module definition. The exporter
preserves explicit versus omitted result types, effects, requirements, import
aliases, public keywords, callback allowances and shorthand expressions.
Finite reduction binders retain their ordered patterns, domains, optional filter
and term. Parser-generated products and lambdas are absent from this view.

Whitespace and comments are not AST nodes. Source spans permit inspecting them
in the exact capture. Syntactically equivalent punctuation, such as a singleton
selector with optional grouping braces, need not distinguish ASTs. An omitted
semantic choice must remain omitted; its inferred value belongs to an
elaboration proposal.

## Root and addresses

The root has exactly `format`, `capture`, `installation`, `sources` and
`declarations`. A source has `module`, `origin` (always `captured`),
`bytes` and `sha256` (64 lowercase hexadecimal digits, without a prefix). A declaration record has `owner` and `nodes`. `owner` is
its canonical authored declaration path; no generated declaration is an owner.

Each node has a discriminating `kind`, `path`, `span` and its syntax fields.
A path is an ordered array of `[category, ordinal]` pairs relative to its owner.
`[]` names the declaration root. Every node address is unique in that owner.
Edges in syntax fields are paths, never private parser array indices, resolved
binding identifiers or machine addresses. The flat node table bounds wire JSON
nesting independently of source depth. Node ordering carries no meaning.

A span has `module`, `begin` and `end`; offsets count UTF-8 bytes and the end is
exclusive. Paths use source order within each category. Renaming a local binder
preserves its path. Inserting a statement changes subsequent statement paths.
Examples:

- `[["input",0],["type",0]]`: the first written input's type;
- `[["body",0],["stmt",2],["expr",0]]`: the third statement's expression;
- `[["clause",0],["subject",0]]`: an inline relation in the first clause;
- `[["spec_block",0],["claim",1]]`: the second claim in the first claim block.

`expr.role_assembly` retains the written role names in `labels` and their
corresponding expressions in `operands`, both in source order. It does not
claim equality of components. The neutral formal term constructor
`formal.role-assembly` retains its ordered `components` argument edges;
role resolution, type/availability checks and leaf layout belong to checked
elaboration. An invalid or unsupported expression role suffix never disappears
from written source, and native elaboration refuses it.

The last mapping is exactly the source-claim address `(owner, block, claim)`.
Clause names and claim labels are syntax fields and do not replace ordinals.
A member definition has its own owner. An inline relation or construction
handler retains its enclosing owner's structural path.

Oracle delivery is an `expr.oracle_send` with written holder followed by
receivers in `roles`, the kind and optional maximum in `arguments`, and data
followed by optional runtime rows in `operands`. An inferred static row count
is absent. `expr.oracle_query` retains handle and position in authored order.
`expr.oracle_contents`, `expr.oracle_rows` and `expr.oracle_forget_rows` retain
their single handle operand. An oracle port additionally retains its written
`oracle_holder` and optional `oracle_maximum` syntax child. Inferred owner,
paired interface leaves and generated shape constants belong to elaboration,
not to this AST.

A layout declaration's `oracle_shapes` list retains its preceding shape
attributes. Each `oracle_shape` node has a `port`, `dimension`, and a static
`bound` child, under the attribute's source span. A bound written there is not
invented as an inline `oracle_maximum` port child. Signature checking resolves
the attachment independently into the checked port's shape metadata.

Sequence expressions have the exact kinds `expr.oracle_sequence_empty`,
`expr.oracle_sequence_append`, `expr.oracle_sequence_at` and
`expr.oracle_sequence_length`. Empty retains the written kind/capacity arguments
and holder-first `roles`; other sequence forms retain ordered operands. No
selected anchor or inferred length is invented in the written tree.

## Node families

Kinds have separate namespaces so equal words cannot confuse types, patterns,
expressions, claims and declarations:

| Family | Syntax carried |
|---|---|
| `type.*` | Named/builtin/formal terms, holes, natural expressions, arrays and tuples; written static arguments, argument labels and explicit role applications |
| `pattern.*` | Names, ignore/unit/tuple/record patterns, optional type, child patterns, record labels and shorthand flags |
| `expr.*` | Written expressions, ordered operands, static arguments and labels, branch payloads, nested bodies, index patterns, roles, `each`, grouping and shorthand |
| `stmt.*` | Binding/assignment/expression/drop/consume/require; written type, roles, site, guard owner and send endpoints |
| `claim_expr.*` | Natural/reference/application/binary/unary/list claim terms, written registry versions, arguments and labels |
| `declaration.*` | Authored declaration kind and header, body, inputs/results, members, clauses, setup, proof/construction choices and claim blocks |

A type node with an authored `roles(...)` suffix additionally has
`role_arguments`, an ordered array of written role names. An annotation inside a
structural type additionally has `components`, its written role-name list, and
`oracle_holder` exactly when an arrow was written. Unannotated ordinary type
nodes retain their existing exact shape. These fields are source syntax, not
ordinary static arguments or inferred agreement. Struct/alias declaration roles
and field order/visibility remain in the existing declaration/port nodes.

A proof's written `public` array contains `input_selector` nodes, retaining the
written input name and dotted field names in order. The source verifier is
implicit in these written selectors; checked Entry selections retain its exact
participant ordinal. Whole ordinary inputs have an empty written path.

The remaining kinds are `body`, `port`, `parameter`, `notation`, `selector`,
`input_selector`, `name`, `requirement`, `clause`, `relation_application`,
`spec_block`, `claim`, `verify`, `setup`, `alternative`, `proof`, `gate`, `application`,
`rule`, `import`, `module_link`, finite `binder` and callback `item_from`.

The existing `requirement.capability` string is the written path of a call-shaped
requirement, including an installed consumer requirement such as
`NativeMessage(T)`. Its `arguments` retain the written type indices. This syntax
slot does not assert capability satisfaction or native authority; declaration
resolution classifies the installed requirement independently. The node shape,
source owner and version are unchanged.

A `proof` node includes a required ordered `gates` list, empty when omitted in
source. Each `gate` child retains its authored span, identifier `path` array and
literal `bits` difficulty. This written order is distinct from the checked
proof-job interface's canonical source-occurrence order. The source AST remains
version 0; old readers and fixtures do not silently omit the new field.

A notation occurrence retains its parsed expression and written operator symbol. Its
selected callable is not an AST fact. A callback's omitted effect allowance is
null even when checking derives a default. A function's written result type is
`result_type`; it does not acquire an authored binder named `result`. Protocol
inputs retain their original combined order, including managed-service and
static callback/domain ports. A relation formal that binds a selector carries
that selector and no inferred type.

Null means the corresponding optional syntax was absent. Empty lists represent
written empty lists or the absence of repeated items; a separate written flag
is present where the distinction determines semantics, including `where ()`.
`public` on a declaration means the `pub` keyword was written; interface member
visibility is independently inferred by elaboration. `effects` records only
written effects. Permission lists retain written order and do not insert the
`Drop` implied by `Copy`. Field ports carry their written visibility; ordinary
ports do not carry a visibility field. Bounds and claim domain spellings remain
unnormalized.

## Layout-source additions

The same version-0 format carries the development layout frontend. A statement's
`evaluation` is `pure` for `=`/`:=`/ordinary expressions, `ordered` for `<-`, and
null for an older-syntax statement. A send's `from` is null when omitted;
`to` remains authored. A single unnamed protocol result has a null port name.
The internal result binder used by checking is not written source.

`section` contains its written `parameters`, `members` and `formal` occurrences.
It is embedded in its enclosing declaration's member list through a `section`
edge. Real enclosed declarations retain their enclosing namespace, with no
section owner inserted. Its parameter nodes do not contain inferred copies.

Declarations and sections have a `formal` list. Its edges address a frozen
**authored formal model**, with the same path and span envelope as ordinary
written nodes. The model has its own typed node references; parser arena indices,
parser-kind names and token lists are not part of the contract. Semantic names
remain unresolved. No clause is elaborated or proved by this representation.

Each kind below has the prefix `formal.`. Fields that reference other nodes
contain paths, and optional references are explicitly null. Repeated fields are
ordered arrays of paths. Field names are also their edge categories; a singular
edge uses index zero. A literal's `literal` field retains its source spelling
(including string quotes). `name`, `symbol` and `notation` are strings.

| Kind | Fields besides `kind`, `path`, `span` |
| --- | --- |
| `reference` | `name` |
| `natural`, `boolean`, `string` | `literal` |
| `hole` | none |
| `group`, `tuple`, `array`, `block`, `parameters`, `static_parameters`, `effects`, `constraints`, `result`, `fields` | `elements` |
| `argument` | optional `label`, `type`, `value`; Boolean `ghost`; `purpose` (`ordinary`, `statement`, `witness`, `parameter`) |
| `call`, `static`, `index`, `record`, `delimited` | optional `function`, ordered `arguments`, `notation` (empty except delimited notation) |
| `member` | `base`, `member`, Boolean `qualified` |
| `prefix`, `postfix`, `infix` | `symbol`, ordered `operands` |
| `roles` | optional `holder`, ordered `participants` |
| `availability` | `value`, `roles` |
| `specification`, `relation`, `ghost_function`, `oracle_function`, `law_declaration` | Boolean `public`; optional `name`, `parameters`, `inputs`, `roles`, `result`, `constraints`, `effects`, `body`, `subject` |
| `requires`, `ensures`, `reduces`, `request`, `alias`, `law` | optional `label`, `value`, optional `residual` |
| `target` | optional `label`, `value`, optional `residual` (null), optional `decision` |
| `security` | ordered `requests` |
| `site` | `value` |
| `import` | Boolean `public`, Boolean `lean`, `module`, optional `alias`, ordered `members` |
| `binding` | `pattern`, `value`, optional `type`; Boolean `mutable`, `ordered`, `update` |
| `return` | `value` |
| `guard` | `condition`, optional `roles` |
| `if` | `condition`, `consequent`, optional `alternative` |
| `match` | `value`, `cases` |
| `case` | `pattern`, `body` |
| `for` | `index`, `lower`, `upper`, `body`, optional `roles`, optional `maximum` |
| `send` | `value`, optional `sender`, ordered `receivers` |
| `query` | `handle`, `position` |
| `oracle-delivery` | `delivery`, `kind`, optional `rows`, optional `maximum` |
| `query-body` | `parameters`, `body` |
| `quantifier` | Boolean `existential`, `variable`, `type`, `body` |
| `lambda` | ordered `parameters`, `body` |
| `reduction` | `symbol`, ordered `bindings` (`pattern` and `domain` paths), optional `filter`, `body` |
| `attribute` | `name`, ordered `arguments` |

A parameter's colon introduces its `type`; a call or record argument's colon
introduces a labeled `value`. `ghost` is retained even when a label is absent.
An ordinary role list has no holder. Custody has a holder and receiver
participants; it cannot collapse into a shared availability list. `group`
preserves one parenthesized argument, distinct from tuple construction.
`reduces` preserves its source relation in `value` and destination in `residual`.
A target's `decision` retains the authored expression after `accept`, or null
when absent; it is not a guessed output or a checked acceptance association.
`security` retains grouping while its child requests retain their own optional
labels. Inline `security: expression` has one unlabeled request child. The word
`security` is not synthesized as that child's label. A `site` node's `value`
addresses the authored selector expression; its envelope `path` still identifies
the written node, as for every other kind. No resolved event identity is inferred
by the writer. These version-0 additions require current producers and readers;
older anonymous-request lookup keys must not be reused as proof evidence.
Clause labels, omitted senders and omitted loop maxima are never synthesized by
this writer. Spans recover punctuation and trivia from the exact capture.

Spec attachment and clause inventory consume the authored model. The native
actual-interface comparison independently checks *attachment coverage* against
captured source headers, using the same syntax implementation. It is not an
independent formal parser or a proof of source elaboration. General formal
elaboration and the corresponding source connection remain separate obligations.

## Limits and assurance

Retention spends checking work before copying headers and bodies. Inspection
rechecks the project's retained work/declaration/operation ceilings, bounds node
traversal and path depth, and serializes under `apiInspectionBytes`. The CLI's
aggregate report ceiling also applies. A limit refusal publishes no partial AST.

The artifact is an input to a future independent checker against the exact
admitted structured snapshot. Name resolution, static substitution, role/purpose
inference, site derivation, projection and realization associations are separate
elaboration proposals. Until their checker and soundness theorem cover a
fragment, `source.correspondence` and `exporter.structured-denotation` remain
named trusted links. Retaining an AST or comparing native exports does not
remove either assumption.


## Source binding proposals

`inspectSourceBindings` exports `zkc.source-bindings/0` beside the AST. Its
root has `format`, `capture`, `installation`, `locals`, `unassociated_locals`,
`declarations` and `units`. A local reference has `kind` (`read`, `call` or `assign`),
`uses` and `binders`. The last two are nonempty arrays of written `{owner,path}` addresses. They retain every
written occurrence of that parser node; a checker must validate the indicated
scope and binding, not pick a same-spelled name from the document.

The lexical resolver records the chosen binder while its scope environment is
live. Input binders translate the separate data/service/callback/domain slots
back to the combined written input order. Pattern binders retain their original
parser-token provenance through record shorthand, loop indices and finite
reduction expansion. Expression indices remain private links into the frozen
written tree. The AST writer itself assigns the exported structural paths;
there is no second path traversal or nearest-span lookup. Alpha renaming changes
names and source bytes, but preserves these binding paths.

Generated syntax can lack a written counterpart. Such records appear in
`unassociated_locals`, with the same kind/address fields and the containing
declaration span (`module`, `begin`, `end`); at least one address list is empty. An empty list
never authorizes a correspondence. An independent consumer determines whether
the source fragment it checks has complete applicable coverage. Private
declarations are retained here, including declarations outside the selected
executable closure.

Independent header replay authenticates every checked declaration's authored
data preconditions, including unused generic and abstract mathematical helpers.
The immutable source inventory determines required replay even when a candidate
erases all its premises. A header with no authored data clauses cannot acquire
candidate premises. The ordered conditions must preserve kind, input positions,
projection paths, axes, and the exact condition and selector source spans;
omission, addition, duplication and permutation refuse. Candidate premise and
path work is charged before snapshot copying and comparison. Additional data
requirements inferred during closed specialization remain subject to its
independent body replay from authenticated root premises.

Static header replay also authenticates the parameter telescope and its resolved
permissions, natural inequalities, symbolic usage bounds and installed capability
predicates. Parameter annotations and inherited module/section contexts count as
source contracts, including on unused generic and abstract declarations. The
immutable source inventory determines replay; candidate flags cannot suppress it.
An explicit `where`, including `where ()`, forbids body contract inference.
Parameter names, atoms, sorts, selected interfaces and static arguments must
retain the interpretation used to resolve the premises. Copy retains its Drop
implication. Natural equality preserves normalized symbolic identities rather
than testing concrete samples. Static premise diagnostic spans do not determine
semantic identity; data-selector provenance above remains source exact.

The original source checker alone owns contract inference eligibility and the
inferred product. After inference finishes, it freezes inferred natural, usage
and capability bounds separately from mutable checked declarations. Header
replay reconstructs authored and signature-derived premises with the existing
lazy signature checker once and freezes that static product as its source-derived
obligation inventory. Later comparisons authenticate inferred additions and
strengthened signature usage leaves against the separate inference product. A
candidate's `inferred` flag is insufficient authority. Explicit/abstract effect ceilings remain source
exact; inferred body effects and results retain their existing body-check owners.
The premise comparison is shared with conformance and View checking; general
header replay does not require equality of unreconstructed body results or
compare generated API artifacts to nonexistent authored signatures.

This retained inference product is native source-check evidence, not an
independent derivation of body inference or a formal elaboration theorem.
Authored premises are reconstructed from syntax; inferred body premises rely on
the original checking lifecycle and its frozen record. Original checked-project
contracts authenticate here. Closed specialization maps and discharges them;
its inferred data requirements remain subject to the separate body replay above.
Variable premise counts, natural terms/factors, telescope strings, static type
arguments, explicit effect dependencies and selector paths are charged before
snapshot copies and comparison. View and conformance reconstruction preflight
every copied declaration, including unused declarations whose effect dependency
maps are unrelated to the header currently being compared.
Static-only comparisons do not copy unrelated admission-origin lists. Data,
consumer and managed-header replay retains its lazy reconstruction when those
contracts apply. No whole-body re-elaboration is required by this comparison.

Retention is charged before storing each resolution record. Inspection shares
one work counter between structural indexing and proposal construction, rechecks
the project's ceilings and bounds serialization by `apiInspectionBytes`. Refusal
publishes no partial proposal.

Each declaration lookup record contains `owner`, `route`, `written`,
`provider`, `target`, `abstract_module`, `source` and `candidates`. Provider and
target are separate `{name,source}` declaration references; `source` is a module
and UTF-8 range, or null for an installed declaration, which has no written
source. An abstract-module term is the resolver's selected binder, or null.
Private and installation references are not filtered through the public API
view.

Every successful declaration-resolution route records exactly one record per
written occurrence and reference position, in resolver order; a lookup whose
result is discarded records nothing. Internally an occurrence uses a retained
syntax-node identity and a position slot, rather than a byte span. Copies used
by inference and replay preserve that identity. Distinct nodes may share a span.
Repeated selected names in one import have distinct ordinal slots.
The checked reference retains typed provider/target/category, binding steps and
abstract context; `abstract_module` is only a presentation projection. Before
independent witness checking, the authored occurrence inventory is frozen.
Replay reauthorizes its routes using source access and rejects changed or missing
candidate references, including provider changes accompanied by changed candidate
metadata. It never appends reference records. Installed declaration replay also
checks exact name, canonical identity, parent, owning module and installation
origin against the frozen declaration index. An association slot and a matching
signature shape do not establish that identity. Missing retained occurrence
handles or syntax refuse with a witness diagnostic.

Ordinary enum construction and Boolean selection take their required producer
from the immutable authored occurrence. Enum occurrences require variant
construction with the frozen resolved nominal instantiation, authored alternative
and ordered payloads, including constructor authority and complete mathematical
admission. And/Or occurrences require selected control in Local and Math, or
their exact implicit Math invocation in Protocol. The expression mapping must
identify that producer's result; Local state joins may project its Boolean
component. Replacing the action, removing its occurrence hint or dropping the
mapping cannot bypass replay. Boolean literals retain their authored constant
and mode, and belong to the immutable required-producer inventory. Their
occurrence is covered only after the exact producer and mapped Boolean result
have been checked; erasing a mapping, with or without its occurrence hint,
does not remove this obligation, including in dormant or captureless bodies.
Every continuing arm of a Local or Math And/Or selection must yield its authored
Boolean tail. Replay follows identity projections and, for Local state joins, the
Boolean first field of the typed tuple pack before following its identity
projections. Mutable state remains in the pack's remaining fields. This
authentication does not evaluate dormant arms or turn selected work into eager
work. Existing source work limits and independent native comparison and
admission remain separate obligations.

Authored scalar decimal literals also require their exact producer and mapped
result, including unused constants and constants in headers, arms and deferred
bodies. Formation retains an immutable resolved carrier and payload using the
ordinary literal rules: index spelling is normalized to its uint64 decimal
value, while field parameters retain their validated spelling and resolved
static context. Replay checks that exact type, constant identity and payload;
candidate types, optional occurrence hints and aliases cannot supply or erase
the source authority. Noncanonical candidate parameters and overflow do not
authenticate a different source literal.
The authored producer envelope admits no static arguments or parameter rewrite
hooks: Local literals use primitive origin, exactly one payload parameter, no
binding arguments and no asset references; Math literals use their literal
payload and no parameters. Both have no operands. Boolean literals obey the
same envelope. Authored `index<N>()` is a separate static call occurrence and
retains its ordinary specialization path.

Administrative result and state carriers use one typed indexed relation.
Unit has no fields; a tuple aggregate has exactly its declared arity and each
operand has the corresponding field type. Explicit-result projections retain
their projected type. Typed identity chains preserve this relation for explicit
results with state, state-only tuples, single direct states and Unit, with
bounded traversal and charged type comparisons.

Oracle queries also belong to the immutable required-producer inventory. Their
mapped result and exact authored position must match the checked query. A
Protocol query retains its exact mapped handle. A query inside an Oracle
definition retains the exact constructor source input reached by typed identity
aliases from the authored handle; another input of the same Oracle type is not
interchangeable. Alias traversal is bounded and charged. Candidate occurrence
hints are optional here and cannot replace operand correspondence or remove the
query's coverage obligation. Native role, shape and dependency admission remains
an additional check.

Mandatory bound-Name reads and binding occurrences come from reachable frozen
syntax and resolved binding categories. Data bindings remain distinct from
managed services, scoped functions and finite descriptors. Each authored data
binding or assignment that constructs a value requires exactly one identity
projection in its expected checked region, with its exact binding and result
spans; a loop index instead requires its source input. Parameter destructuring
retains its source parameter and field path. An initializer that always stops
constructs no binding value. Candidate values supply proposed local types only
after this coverage is authenticated. Moving or erasing a candidate span,
mapping or optional occurrence hint cannot turn an ordinary resolved Name into
an unrecognized read. Initializer identity, projection paths and mutable
generations remain separate checked obligations.

Expected mutable generations are derived from retained authored evaluation
structure before candidate operation traversal. Read, after-header capture,
definition and control-join events are distinct. Each authenticated lexical
region indexes its own definitions and joins, seeded by its enclosing input
snapshot. A control captures state after evaluating its headers; a deferred
body captures at its eager creation event, before later arguments can mutate
state. Incoming control operands retain their source binding and projection
path, using the shared source free-place relation and ordered state roots;
overwriting a state before its first read does not authorize another binding.
Actual SSA transitions must authenticate those snapshots and the latest
continuing state. Formation freezes the exact initially available and continuing
state bindings using ordinary usage resolution. Replay checks that membership,
including an unused joined state; a candidate cannot choose which states were
consumed. Source writes invalidate old generations even if the candidate
removes an entire state join. This relation does not sort candidate operations
by spans and permits independent administrative reordering. Zero-trip loops,
consumed states and stopped arms retain their existing outcome obligations.
Finite descriptor recipes retain their eager resolved operand references in the
immutable source record. A protocol repeat's recipe-capture suffix must match
those available source values through typed identity edges and validated
type-preserving participant restrictions. Each immediate identity edge preserves
participant availability, oracle holder and ordinary data placement. Comparing
only compressed endpoints is insufficient: an intermediate edge cannot discard
and then restore that metadata. Identity edges cannot restore components
discarded by a restriction. Restriction inputs
must precede their producer, retain ordinary data placement and supply every selected participant;
they cannot gain participants. This equivalence is specific to recipe captures,
whose final availability is exactly the intersection of the eager operand's
participants and the loop roster. Traversal and type/participant comparisons
debit the existing source work budget. It does not reread mutable bindings at
loop entry. Ordinary captures retain the entry-generation rule. This preserves
earlier descriptor snapshots and non-place operands while
rejecting changed, missing or additional recipe captures.

Construction initializer and codec references retain their exact authored
occurrence, including inherited references and substituted arguments. A valid
provider at another occurrence cannot authorize a changed projection. Replaying
a generic construction must preserve its deferred boundary requirements; it does
not infer concrete admission from a symbolic provider.

Body replay binds each selected arm, repeat and extracted callback to its
expected authored lexical region and mode. Moving an otherwise valid occurrence
to another arm refuses. Transparent blocks share their enclosing checked region;
eager Boolean operands and Local short-circuit arms follow their respective
source evaluation rules. Managed roots come from authored service inputs and
lexically visible aliases, independently of candidate capture slots.

Every authored lexical body also authenticates its guaranteed-stop status
against frozen syntax, independently of candidate stop flags and effects. A
reachable explicit stop requires its exact authored reason and no results.
Transparent blocks forward their exit. If every arm of an If, Match or Boolean
selection stops, the containing body is guaranteed to stop, but its own
terminator is unreachable: replay imposes no parent reason and checks each
child region's reachable reason separately. This remains true when native Match
alternatives reorder the written arms. A For body can stop without making its
parent guaranteed to stop, because the loop may execute zero times; a callback
body is deferred. Both bodies are still checked, including dormant regions and
unused callbacks. An implicit Protocol Math Boolean wrapper derives its exit
from the selected expression, while using the containing Protocol region for
lexical membership. Exit derivation is memoized under the shared source work
allowance and uses an explicit worklist rather than another depth limit.
The same source inventory requires every reachable control occurrence exactly
once in its expected region, including continuing selections and loops.
Missing, duplicate or misplaced controls refuse independently of candidate
results, mappings, stop flags and effects. The selected expression's implicit
Protocol Math wrapper has its own inventory within the containing lexical
region. This control coverage authenticates the region mapping consumed by
binding replay; it does not assign a reason to an unreachable parent terminator.
Generated Oracle predicates inventory only syntax reachable from their actual
root. Inventory construction, region mapping and binding replay share the
existing bounded source work allowance.
Generated bodies without an authored lexical region retain their existing
operation, effect and admission checks.

`route` names the resolution route:

| Route | Records |
|---|---|
| `path` | A written path in a signature, associated type, constraint, conformance contract, construction provider, body callee or type, including qualified paths without an import and names selected from the explicit prelude |
| `import`, `import-name` | An import's module and each selected name; a facade keeps its facade provider |
| `method` | A home method keeps its selected home provider, including a catalog-authorized forwarding home, and canonical implementation target. A managed method keeps its constructor's authored provider route, including a facade, and its indexed installed method target |
| `module-member` | An associated type or callable member of a bound module parameter; the interface-bound route keeps its provider and `abstract_module` is its binder |
| `service` | A managed service constructor in a protocol port; the port retains its selected provider and canonical installed constructor even through an import-free facade path |
| `notation` | An operator, delimiter, indexing or reduction use, once its callee is fixed. The provider is the module whose declaration or body introduces the selected binding, which is the installed module for prelude operators; the target is the selected, or filtered, callable |
| `construction` | A construction provider's interface member: `State`, `initialize`, `Record`, `write` and `finish`. The provider is the selected implementing-module route; a symbolic provider keeps the written route of its interface bound and its binder as `abstract_module` |

Records are source occurrences. They stay separate from the deduplicated unit
dependencies in `units`, which has one row per captured unit, sorted by module
path: `module`, its [source authority](definitions.md#source-authority)
`revision`, and `dependencies`, the sorted module paths of its direct
dependency units. A unit's closure and its edges follow from these rows.

Declaration lookup can precede body parsing. Its `candidates` therefore contains
**all** AST addresses with exactly the observed source range, including different
node kinds at an equal span. The array may be empty. It is a search hint, not an
assertion that one of these nodes is the lookup occurrence. No nearest-span
fallback or arbitrary first match is selected. The independent checker must
recompute the occurrence and route against the written modules and imports.

Closed substitutions are recorded in the source-instance export below.
Call-edge correspondence, role/port inference, control, notation and oracle
proposals remain separate obligations; the independent checker and its
soundness theorem are still required.

## Checked source artifact

`exportSourceCorrespondence` and `zkc-compile language-check
--subject=MODULE::Protocol --source-correspondence` publish a
`zkc.source-correspondence/0` object. The CLI nests it under
`source_correspondence`. A proof Entry can replace the explicit subject.
Ordinary Host functions are outside the structured protocol export profile.

The root has exactly `format`, `admission`, `source_ast`, `bindings`, `snapshot`,
`instances`, `instance_rows`, `generated`, `generated_rows`, `occurrences` and
`rows`. `admission` is the same association used by the
[source-claim export](claims.md): original-byte SHA-256, protocol symbol,
interface SHA-256, capture and installation. `source_ast` and `bindings` use the
formats above. `snapshot` is the actual [structured source](../formats/structured-source.md)
export of that checked original. No separate subject digest is introduced.

Each `rows` element has `row`, `operation`, `derivation`, `original` and `sources`.
`row` follows array indices in that exact snapshot. `operation`, `derivation`
and the nullable original lexical range come from the structured encoder's
[association table](../formats/structured-source.md#native-row-associations).
They are produced in the same call that emits the snapshot. The original range
has `begin`, `end`, `line` and `column`.

`sources` retains every captured-source span at that parsed MLIR
position. Installed declarations retain their original-row association with
empty `sources`; no zero-length written span is invented for an installation. Each element contains `span` and `candidates`. Candidates are all
written `{owner,path}` nodes with exactly that span. They are search hints;
there is no nearest-span match. Empty sources or candidates remain explicit,
including generated rows with no authored node. A row is never silently omitted
because its source association is missing. Diagnostic filesystem paths do not
enter the artifact.

Component export ceilings still apply. The join has its own bounded work counter
and charges source positions, syntax paths and copied candidates before storing
them. The complete publication is bounded by `apiInspectionBytes`, including
all components, and a refusal returns no partial document. The retained original
and interface must fit the requested ceilings too.

`checkSourceCorrespondenceExport` checks publication integrity against this
canonical producer, accepting JSON whitespace/member-order differences and
refusing duplicate keys, unknown fields and changed components. It does not
admit a new original and is not the independent Lean checker. This artifact
currently supplies written syntax, binding observations, closed substitutions
and source-to-row associations. Call-edge, notation/scoped extraction,
role/control and oracle elaboration proposals remain to be added. Neither native comparison nor a location join
removes the parser, source-correspondence or structured-denotation trusted links.

## Closed source instances

`inspectSourceInstances` exports `zkc.source-instances/0`, with `format`, `capture`,
`installation` and `instances`. Each retained closed instance has `symbol`,
`template`, `statics`, `scoped`, `domains`, `layout` and `oracle_obligations`.
Oracle instances additionally have `oracle_definition`. The symbol is an actual
closed declaration name. No consumer decodes its hash to establish source origin.

A declaration template has `kind: "declaration"`, its canonical `owner`, a
`generated` flag, its source span and exact-span `candidates`. An installed
declaration has `source: null` and empty candidates: its authority is the
installation, and it has no captured written source. A scoped template
has `kind: "scoped"`, its lexical owner, source span and exact written `nodes`.
The latter uses retained expression provenance, never the generated helper's
private expression number. Empty nodes remain explicit for generated adapters.
Candidates remain search hints; a source correspondence checker must validate
the template and substitution.

`statics` contains `[parameter-name, term]` in declaration order, using the
[closed source-term grammar](../formats/structured-source.md#definition-origins).
`scoped` contains actual selected callback symbols in parameter order. `domains`
contains closed descriptor constructor graphs: `inputs` are closed source
terms; `nodes` have exactly `kind`, `contract`, `operands`, `children` and
`axis`; `result` selects a node and its complete result contract. `contract`
is the complete closed descriptor source term, using its installed constructor
and ordered typed arguments (currently `["builtin", "finite", [item-term]]`).
Operands select this descriptor's ordinary input signature. Each child is
exactly `{ "node": prior-node-index, "contract": descriptor-term }` and must
match that node's complete contract independently of the parent's contract.
Node and edge contract arity and every typed index are retained; no item-only
field or graph-wide family substitutes for them. Kinds are `elements`, `indices`, `range`, `zip`, `product`, `matrix_row`,
`matrix_column`, `matrix_coordinates` and `source_array`. No open parameter or
factory node, internal shape key, or caller SSA value is serialized as a domain.
Finite leaves retain this version-0 shape without an item-only compatibility
reader. A structural argument uses the explicit
[descriptor formation envelope](descriptor-formation.md#closed-source-export).
Finite remains the installed native leaf/consumer family. Independent Lean
descriptor interpretation remains unimplemented.

`layout.inputs` and `layout.captures` retain the closed source callable's alias
partition in source argument/hidden-capture slots. They are not flattened
structured-IR operand indices. An extracted callback's lexical data captures
are ordinary helper inputs after its explicit arguments. Hidden captures at the
caller carry the selected callback's environment or a domain's runtime operands.
The two lists must not be conflated with lexical free variables. Domain and
capture interpretation must be checked against the actual selected body.

These are declaration substitutions. A finite operation can carry a closed
domain and callback directly without instantiating a declaration with domain
or scoped arguments; the presence of finite operations does not imply nonempty
`domains` or `scoped` here.

`oracle_definition` retains the checked oracle plan: `source_count`,
`query_parameter` (`name`, `type`, constructor-excluded `input` slot), `answer`,
`admissibility` (qualified source name), `admissibility_id` (checked declaration
index), `admissibility_symbol` (actual Formula symbol), `admissibility_inputs`,
`admissibility_companions`, `predicates`, `source_bounds`, `result_shape` and
ordered `queries`. Input entries have `name` and diagnostic `type` spelling.
Authored predicate entries have `ordinal`, nullable `label`, checked Formula
`condition` value index, `begin` and `end`. Source bounds have `source`,
`dimension` and `maximum`; result shapes have `dimension`, `input` and `maximum`.
Queries have `source`, `position`, `answer` and nullable `site`. Type and bound
spellings describe the plan; consumers check actual source terms and the Formula
body independently. Declaration and public API inspection expose the same plan
for templates as well.

`admissibility_companions` contains `template` and `instance`. The first is the
whole-predicate [companion address](companions.md#virtual-oracle-admissibility);
the second selects this closed oracle's symbol, or is null for an open template
in declaration/API inspection. These are definition addresses, never evidence.
Requested component, serialization and work limits apply at export; an identity
failure refuses the whole export without partial output or placeholder keys.

Every instance has an `oracle_obligations` array, empty when its body contains
no oracle constructions. The traversal emits every retained construction in
body order, entering nested regions at their enclosing operation. Each row has
`path`, `source`, nullable `site`, `definition`, `admissibility`, `companions`,
`substitution`, `holder`, `receivers`, `results` and `status: "unresolved"`.
`definition` selects the actual oracle instance; `admissibility` selects its
actual generated Formula symbol. `companions` is that definition's
`admissibility_companions` object. A repeated construction can share both lookup
addresses while retaining its own obligation. Definitions without constructions
have addresses but create no occurrence rows.

`path` is a nonempty sequence `[operation, region, operation, ...]` starting in
the enclosing instance body. A repeat's only region is numbered zero; local
control regions use retained order. `source` has `module`, `begin` and `end`.
`holder` and ordered `receivers` use the enclosing checked declaration's role
indices. `results` are construction result value indices in the selected body.
Region depth and traversal share the requested expression-depth and work limits.

`substitution` retains constructor order. Each entry has `input`, `value`,
`type` and `projection`. `input` selects the Formula input; `value` selects an
actual value in the body selected by `path`; `type` is its complete closed
source-term encoding. Direct source inputs use `projection: "data"`: the value
is a logical source handle whose Data supplies that Formula input, retaining the
anchor's exact custody and immutable shape. Remaining ordinary captures use
`projection: "value"`. There is no query-parameter argument to admissibility.
These are source SSA indices, not structured-IR operand indices. Consumers check
region capture mappings, exact types, nominal statics and the actual Formula
application independently. Publication is unconditional on optional security
checking and neither proves the application nor inserts a runtime guard.

The combined source artifact adds `instances` and `instance_rows`. The former is
this document; the latter contains one `{instance,rows}` entry per instance.
`instance` is an ordinal in this export, and `rows` is every matching symbol row
in the actual snapshot's domain, relation, binding and definition tables. Empty
rows remain explicit for closed declarations without a standalone exported row.
The association never guesses a definition from its printed name.

Explicit and inferred event labels are authenticated against the frozen written
statement in its lexical region. Replay reconstructs the default from the
ordered binding or repeat index and derives the required outer event family from
immutable syntax and authenticated source-call resolution. Messages, managed
queries, protocol calls, Oracle construction, Oracle queries, sequence append
and selection, selected control and protocol repetition retain their distinct
families. A query in an Oracle definition is a source query; a Protocol query is
a receiver event. A candidate action cannot select its own source obligation.

Replay matches exactly one event of the required family at the exact authored
outer span in the same lexical region, and rejects missing, added, swapped or
duplicate candidate labels. Replacing a query with pure computation or another
event family does not discharge that obligation, even for an unused answer.
Removing optional expression hints or source-to-value mappings cannot erase it.
An inferred ordered binding has no protocol site only when its source resolves
to a non-event computation, including a legitimate Local call; missing call
resolution does not establish this exception. Explicit labels still require an
eligible event. Eager Protocol Boolean helpers, scoped mathematical bodies and
generated Oracle predicates do not inherit unrelated protocol labels from their
shared source syntax. Source indexing, call resolution indexing, exact-span
matching, operation traversal and label bytes use the bounded work allowance.

### Generated definitions and occurrences

Emission assigns every native site and creates every generated helper, and it
records both for the exact bytes it prints; the artifact projects that record,
so there is no second site derivation.

```text
generated      := [{symbol, purpose, part, origins: [{definition, site}...]}...]
generated_rows := [{generated, rows: [[table, index]...]}...]
occurrences    := [{definition, site, nodes: [{owner, path}...]}...]
```

`generated` lists every definition that emission generates for a source
operation rather than closing from a declaration. `purpose` is `control` (an
outlined control region or check arm), `custody` (an outlined custody
operation), `finite` (a finite domain, callback or array adapter) or `map` (a
shared map domain or body adapter); `part` is the emitter's local
discriminator, such as an arm label, `domain` or `body`, or the custody
primitive. `origins` lists, sorted and unique, every `(definition, site)` that
created or reused the helper: the definition holding the creating instruction
and that instruction's site. A pure mathematical instruction publishes no site,
so its origin keeps the site emission assigned it. A control region is
published inside the definition whose instruction enters it, so its sites and
origins name that definition. `symbol` is unique, and so is
`(purpose, part, origins)`. `generated_rows` has the shape of `instance_rows`.

`occurrences` has one row per nonempty site of every snapshot definition,
including nested regions and stop terminators, in definition order and then
block preorder. `nodes` is exactly the written-index entry of the originating
expression of the source operation the site was emitted for, within that
operation's lexical owner. Checking sets the originating expression on every
operation it emits; specialization preserves it, and its comparison refuses a
changed one. Operations derived from one expression share it, so several sites
may share nodes. A site with no expression has `[]`; an expression without a
written node refuses the export, and a span never selects a node. Every node is
kept.

Before publication the producer enforces the completeness invariant, which
`checkCorrespondenceInventory` also checks: every domain row and every
function or oracle definition row of the snapshot is the symbol of exactly one
`instances` or `generated` entry; every realize, finite, collect and map row has
its `computation` row association; binding rows are identified by their
contract and arguments. A row of another producer is a new `purpose`, never an
exemption. Occurrence rows cover every nonempty site in canonical order, including
virtual oracle bodies. An empty written-node list does not waive site coverage.
Every origin names a snapshot definition. The export check is canonical
equality, so any edit refuses.

Occurrences, `generated` entries and their `origins` are exact-artifact
associations, not edit-stable author addresses: a new use changes sites, paths
and origins. Lean keys companions on authored owners, template or instance
symbols and [companion keys](companions.md), and reusable generated-body laws
on `purpose` and `part`; it does not key on site names, occurrence rows,
`origins` or generated symbols. An ordered occurrence path comes from
traversing the exact snapshot's applications, repeats and regions; `origins`
is provenance, never call ancestry.
