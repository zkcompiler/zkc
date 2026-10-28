# Written source AST

`zkc-compile language-check --source-ast` adds a `source_ast` member containing
`zkc.source-ast/0`. The corresponding C++ API is `inspectWrittenSource`.
The artifact retains written syntax for the independently checked source
correspondence connection. It neither admits an IR nor certifies elaboration.

The parser is a named trust boundary. `capture` binds captured modules and
assets; `installation` binds installation sources. Each source record contains
its logical module, origin, UTF-8 byte length and SHA-256. Diagnostic filesystem
paths are excluded. All captured and installation declarations are present,
including private ones. This artifact has different consumers from the public
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
`declarations`. A source has `module`, `origin` (`captured` or `installation`),
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

The last mapping is exactly the source-claim address `(owner, block, claim)`.
Clause names and claim labels are syntax fields and do not replace ordinals.
A member definition has its own owner. An inline relation or construction
handler retains its enclosing owner's structural path.

## Node families

Kinds have separate namespaces so equal words cannot confuse types, patterns,
expressions, claims and declarations:

| Family | Syntax carried |
|---|---|
| `type.*` | Named/builtin/formal terms, holes, natural expressions, arrays and tuples; written static arguments and argument labels |
| `pattern.*` | Names, ignore/unit/tuple/record patterns, optional type, child patterns, record labels and shorthand flags |
| `expr.*` | Written expressions, ordered operands, static arguments and labels, branch payloads, nested bodies, index patterns, roles, `each`, grouping and shorthand |
| `stmt.*` | Binding/assignment/expression/drop/consume/require; written type, roles, site, guard owner and send endpoints |
| `claim_expr.*` | Natural/reference/application/binary/unary/list claim terms, written registry versions, arguments and labels |
| `declaration.*` | Authored declaration kind and header, body, inputs/results, members, clauses, setup, proof/construction choices and claim blocks |

The remaining kinds are `body`, `port`, `parameter`, `notation`, `selector`,
`input_selector`, `name`, `requirement`, `clause`, `relation_application`,
`spec_block`, `claim`, `verify`, `setup`, `alternative`, `proof`, `application`,
`rule`, `import`, `module_link`, finite `binder` and callback `item_from`.

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
root has `format`, `capture`, `installation`, `locals`, `unassociated_locals`
and `declarations`. A local reference has `kind` (`read`, `call` or `assign`),
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
the source fragment it checks has complete applicable coverage. Private and
installation declarations are retained here, including declarations outside the
selected executable closure.

Retention is charged before storing each resolution record. Inspection shares
one work counter between structural indexing and proposal construction, rechecks
the project's ceilings and bounds serialization by `apiInspectionBytes`. Refusal
publishes no partial proposal.

Each declaration lookup record contains `owner`, `written`, `provider`, `target`,
`abstract_module`, `source` and `candidates`. Provider and target are separate
`{name,source}` declaration references; `source` is a module and UTF-8 range.
An abstract-module term is the resolver's selected binder, or null. Repeated
resolver observations are retained in their original order. Private and
installation references are not filtered through the public API view.

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
`instances`, `instance_rows` and `rows`. `admission` is the same association used by the
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

`sources` retains every checked-original source span at that parsed MLIR
position. Each element contains `span` and `candidates`. Candidates are all
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
`template`, `statics`, `scoped`, `domains` and `layout`. The symbol is an actual
closed declaration name. No consumer decodes its hash to establish source origin.

A declaration template has `kind: "declaration"`, its canonical `owner`, a
`generated` flag, its source span and exact-span `candidates`. A scoped template
has `kind: "scoped"`, its lexical owner, source span and exact written `nodes`.
The latter uses retained expression provenance, never the generated helper's
private expression number. Empty nodes remain explicit for generated adapters.
Candidates remain search hints; a source correspondence checker must validate
the template and substitution.

`statics` contains `[parameter-name, term]` in declaration order, using the
[closed source-term grammar](../formats/structured-source.md#definition-origins).
`scoped` contains actual selected callback symbols in parameter order. `domains`
contains closed finite constructor graphs: `inputs` are closed source terms;
`nodes` have `kind`, `item`, `operands`, `children` and `axis`; `result` selects a
node. Operands select this descriptor's input signature and children select prior
nodes. Kinds are `elements`, `indices`, `range`, `zip`, `product`, `matrix_row`,
`matrix_column`, `matrix_coordinates` and `source_array`. No open parameter or
factory node, internal shape key, or caller SSA value is serialized as a domain.

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

The combined source artifact adds `instances` and `instance_rows`. The former is
this document; the latter contains one `{instance,rows}` entry per instance.
`instance` is an ordinal in this export, and `rows` is every matching symbol row
in the actual snapshot's domain, relation, binding and definition tables. Empty
rows remain explicit for closed declarations without a standalone exported row.
The association never guesses a definition from its printed name.
