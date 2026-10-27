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

Specialization, role/port inference, control, notation and oracle proposals remain
separate obligations; the independent checker and its soundness theorem are
still required.
