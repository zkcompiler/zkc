# Resolved authoring and static construction

This profile defines the boundary between protocol authoring and explicit common
PIR. It extends the source reading route; it does not change the meanings of
messages, challenges, local computation, rejection or resources. The
[implementation guide](../../../compiler/frontend.md) states native
coverage and limits.

## Subjects and judgments

An authoring subject consists of frozen syntax and its supplied dependencies.
Analysis resolves declarations in scopes, reconstructs source types and records
static selections. A declaration reference identifies a declaration within that
subject; it is not a portable artifact identity. A source span locates spelling
and is excluded from semantic identity.

Distinguish these judgments:

1. **Syntax formation:** the text supplies a complete declaration or body.
2. **Source formation:** references and source types are resolved under the
   declaration's parameter context; source abstraction rules hold.
3. **Concrete elaboration:** a selected source subject produces explicit common
   PIR with no unresolved authoring-only choices.
4. **PIR admission:** the actual emitted program satisfies the existing domain,
   interaction, resource and construction rules.
5. **Property evidence:** a stated property holds for its identified subject under
   its stated premises.

None of these is a synonym for another. Protocol family bodies are source-checked
under their bound parameters and declared requirements. Common admission judges
concrete selections. Neither this source
judgment nor its selected instances establishes a universally quantified PIR
admission or security theorem over all possible domains. A partial editor model
may retain valid declarations and errors, but is not a complete subject for
accepted emission.

A readable common-carrier representation is distinct from library authoring.
The explicit `carrier module` form preserves emitted names and logical origins,
including reserved generated symbols, without treating the producer of the text
as an authority. It is self-contained and cannot declare imports, exports,
source interfaces, components, source records or relation assets. It admits the
same portable function, binding, configuration, protocol, instance and entry
records as the corresponding carrier. Reading it still checks formation and
PIR admission; printing it must round-trip to the exact same carrier. It cannot
be captured as a source library or child module, and does not recover private
library interfaces from emitted code. Construction uses the carrier's existing
selector interpretation, without applying source-project aliases again.

## Captured projects

A source project contains immutable source files with logical module paths,
explicit exact library dependencies and captured relation assets. Physical paths
locate diagnostics and inputs; they do not establish declaration equality.
Importable roots declare namespace, name, version and captured resolution. An
anonymous application owner is local and not an importable package. The installed
contract owner is reserved to the compiler's installed catalog. The captured
libraries are exactly the application's transitive dependency closure: a
captured root that no owner in that closure depends on refuses. Identity, logical
origins and acceptance are therefore functions of the declared dependency graph,
never of which additional files were supplied.

Resolution binds imports and reexports to exact declarations. Aliases preserve
identity; private declarations are available only within their defining module
and descendants. Public signatures cannot leak inaccessible concrete declarations.
Dependency and alias cycles refuse. Source resolution neither chooses a package
version nor trusts an ambient declaration with a matching printed name.

Reference authorization is category-specific. Runtime value binders do not
shadow type, static or module paths. Quoted exact authored names still require
lexical visibility; generated implementation symbols are not source authority.
An authored name may contain dots. An unquoted dotted reference that names such
a declaration in scope and is also a path through modules, imports or a
dependency refuses as ambiguous, whether or not the path's target is visible
there. Both candidates must authorize the complete reference in the requested
category; a namespace prefix alone is not a competing declaration. Quoting a
call or a declaration reference names the authored declaration. Other categories
require an unambiguous spelling or alias, since quoted type/static vocabulary
already has its own meaning.
A nominal declaration can share a printed spelling with an installed type because
its resolved identity and emitted symbol are distinct. It affects only references
that resolve to that declaration, never installed references in another module.
Opaque operation attributes remain data except for the contract's designated
numeric slots. An explicit qualified primitive call and a quoted, lexically
visible exact helper call keep different categories even if their textual names
coincide. Neither may silently fall back to the other.
Convenience profiles are application-root authoring choices and
do not supply implicit domains or implementations to imported definitions.

An owner's checked environment includes its declarations, the direct public
dependency interfaces and their reached public signature closure, plus installed
contracts. A dependent's private declarations cannot change that environment.
Private implementation closure is linked from separately checked bodies.
Reanalysis after an interface, label, body or captured-subject change must check
the affected judgment again; retaining a name or digest is not evidence reuse.

Output names are collision-checked locators, separate from exact identities.
An authored declaration name cannot take the form of a generated one, so
whether a project is accepted never depends on a generated digest or counter
coinciding with an authored spelling.
Logical origins remain distinct from implementation symbols. Cross-owner origin
collisions qualify every owner; an ambiguous unqualified selector refuses.
Application-root functions may explicitly share an authored logical origin, as
materialized relation functions do. This groups observations; it does not equate
the functions or grant declaration authority. Such a group cannot claim an
automatically allocated declaration/member origin or a captured relation origin
owned by another authority. Imported and child definitions cannot override their
allocated origins with application-root origin syntax.
Construction selectors are resolved against the same captured subject: a
logical definition and a selected configuration are distinct selector targets.
An ordinary function selector selects that function's primitives and their
expanded copies, including the copies an imported function's entry and links
carry; for an explicit origin-group member it does not select the other members
of the group. Generic definition selectors retain their logical
definition identity, and configurations retain their selected callable identity.
The entry identifies the protocol instance separately from draw selection. An
origin group selects actual matching occurrences, not every function in the
group. Authored function groups are resolved before normalized site identities;
an unrelated helper call cannot change their selection. A source path that
also denotes another owner's closed origin or symbol refuses as ambiguous.
No general refactoring-to-wire-identity theorem follows.

## Names and types

Resolution chooses the declaration category before checking the call. A failed
operation call must not silently become a user function call. Static domain
parameters are bound declarations, separate from runtime value variables and
participant roles. Associated domain members are projections of domain terms,
not fields read from runtime values. Only explicit associated-member syntax
forms a source projection; the dotted spelling of an opaque identity is not an
implicit projection. A quoted root denotes a concrete identity, not a bound
parameter. Emission must preserve the distinction
between a bound parameter and a concrete identity even when spelling collides;
a carrier that cannot encode the distinction must rename lawfully or refuse.

A source type is a logical type application, an instance of a nominal
record declaration, an ordered product of source types, or a finite homogeneous
array with a retained element type and count. The empty product
is unit; singleton products remain distinct from their element type. Product
equality compares element types recursively and preserves nested record identity. Domain terms distinguish concrete identities, bound
parameters and their associated projections. Two records with the same leaf
layout remain different source types. Two distinct domain parameters may select
the same domain; substitution need not be injective. An array is not a product,
and zero length does not erase its element identity before source checking.

A record construction checks its declared fields, static arguments and constructor
authority before layout erasure. Field expressions execute exactly once in written
order. Layout determines the order of the resulting leaves and does not license
reordering computations. Calls and returns check nominal source compatibility
before passing flattened leaves to PIR.

A checked record restricts construction to its declared constructors. This rule
alone proves no mathematical predicate about its values. Unchecked host inputs
or a bodiless external callable cannot manufacture a checked result, including
one nested inside a record or product. An external-validation route would require a
separately defined contract and is not supplied by a type name.

## Local values and distributed ports

A local product is one value owned by one participant. Its layout is the ordered
concatenation of its element layouts; unit has no leaves. Formation and annotation
checking precede erasure. Product formation does not copy resources or change their
usage contracts. Reusing the same affine leaf through distinct projections or
aliases remains reuse of that leaf in common admission.

A participant placement block checks in a lexical environment containing only
that participant's available values. The block uses the same local computation
language as a function. Its final expression (or final explicit return) yields a
local value; its internal bindings do not escape. Closure conversion creates a
local algorithm and passes exactly its used free leaves. It must not capture an
unused resource or a peer's private value. Communication remains a separate
protocol action; it is not inferred from a local reference.

Named call arguments and record fields evaluate once in their written order.
The resulting values are arranged in signature/layout order. Reordering the
computations to achieve that arrangement is not justified by this rule.

Protocol outputs are distributed ports, each with a type and owner. They are not
a tuple located at one participant. When named, all ports have distinct names.
A named protocol completion or child-result binding covers each declared port
exactly once. It preserves declared port order, type and role ownership;
reordering source labels never transfers a value between roles. Terminating a
protocol does not itself assert acceptance or discharge a claim.

## Static construction

Named static constants denote pure bounded natural computations. They cannot read
participant inputs, execute cryptographic operations, perform I/O or inspect runtime
state. Dependency cycles, undefined references, invalid arithmetic and exceeded
construction budgets are refusals, not default values.

Static substitution acts on structured references and terms. It does not replace
arbitrary occurrences of text in schema names, operation labels, quoted attributes
or user declaration names. Runtime bindings keep their lexical meaning. A quoted
literal is not made into a static reference merely because its text matches a
constant or parameter.

A protocol family binds domain parameters and declares requirements. A concrete
selection supplies actual domains; the existing domain/requirement rules check
those actuals. Construction substitutes domain terms in interfaces and designated
uses, selects local algorithm configurations and resolves child protocol uses.
It preserves the ordered interaction body, role ownership and message schemas.
A direct entry may construct a closed instance tree from declared dependencies
when its domain choices and natural parameters are fully supplied. Missing
parameters, dependency cycles and ambiguous or invalid targets are refusals;
entry shorthand does not choose a backend or invent an interaction.
The selected interface must equal substitution of the source interface, including
nominal record identity; independently accepting both signatures is insufficient.
The same source type/role checks apply to an explicitly authored concrete
protocol. Each selected concrete program then undergoes ordinary PIR admission.

Generated declaration names are deterministic functions of retained source choices
and the specified naming policy. They must not depend on addresses, filesystem
paths or hash-map iteration order. The particular spelling of a generated name
can affect existing artifact identity; determinism is not a general promise of
alpha-equivalence. Identity claims use the selected
[artifact contract](../../realization/artifacts.md) and
[compiler identity policy](../../../runtime/artifact-identity.md).

## Lowering and retained information

The source semantic model retains the declarations, source types, references and
instantiation origins required by its current consumers. Lowering may erase an
authoring distinction after its last required check, but an erased carrier cannot
later be used as evidence that the original distinction was checked. Future
separate interfaces must retain their own checking subject and bind it to the
actual implementation.

The common PIR carrier is a separate representation. JSON or programmatic PIR
producers do not acquire source-language guarantees by using the same flattened
layout. They pass the same common admission rules. Likewise, retaining a typed
source analysis does not bypass those rules or establish cryptographic security.

The implementation may combine checking and construction of a lowering plan in
one traversal. The semantic requirement is that the necessary source distinctions
remain available until checking is complete and that emission consumes the actual
resolved result. A separate source execution evaluator is not required.

## Formal correspondence and trust

`Zkc.Source.Region.denote_instantiate` and `Region.run_instantiate` state type
substitution preservation for structured source and its selected operation
interpretation. The latter compares complete executions, including failure and
retained event prefixes. `Region.denote_renameDefinitions` additionally requires
correspondence of actual selected callee meanings; matching signatures is not
sufficient.

These laws state the obligations of elaboration. A serialized report or a
matching hash does not discharge a source-erasure obligation.

Static interfaces, private component representations and coherent library linking
are defined in [checked libraries](checked-libraries.md). Abstract values retain
their usage obligations even when their selected storage representation is empty.
