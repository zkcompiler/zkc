# Normalized artifact identity

This page owns the normalized identity contract. It extends the
[concrete artifact format](../compiler/artifact-format.md); the common process semantics and
installed Merlin suite remain unchanged. Source admission and exact construction
checking still precede artifact execution. This profile defines compatibility
under the transformations listed below, not an equivalence decision procedure
for arbitrary protocols or a Fiat–Shamir security theorem.

## Policies and source custody

Keep the immutable original carrier as the admission, construction-checking and
custody subject. A `zkc.construction/1` descriptor's last field names its
identity policy: `normalized` or `exact`. The two policies are both current;
the field is a choice, not a version, and a later policy adds a value rather
than a tag. The source notation defaults to `normalized`. Normalized identity is
supported with explicit-binding protocol and `zkc.library/1` sources. Exact
identity keeps the whole-source root of the [artifact format](../compiler/artifact-format.md).
Both roots share the tag `zkc.artifact-binding/1`; the descriptor inside each
names its policy, so the two cannot coincide.

For normalized identity, derive a resolved copy from that original source. All nonterminal
instruction sites in each function or protocol are renamed `site0`, `site1`, ...
in depth-first preorder, entering a loop body immediately after its loop node.
Counters restart at each declaration. Return/yield do not consume a counter.
These are ordinary valid source identifiers; no carrier grammar extension or
special numeric-name class is necessary. Rename simultaneously, never by global
string replacement. Repeated execution still appends call ancestry and loop
iterations to the existing logical-origin encoding.

The resolver rewrites generic `using` keys through the final target definition's
site map, descriptor draw sites through their function, generic definition or
configuration, and application receive sites through their instance's protocol.
It does not rename definition/configuration/instance/entry names, role names,
public port names, schemas, static parameters, cryptographic identities or
attributes. Missing or ambiguous references fail. Complete original-source
admission precedes using the resolved view. Each implementation computes the
view from source, never accepts an unchecked producer-supplied map.

A draw selector is resolved through one site map: a function's own, a generic
definition's, which every instantiation shares, or a configuration's final
definition's. An explicit origin group that is not itself a declaration has no
site map, because each member function numbers its sites separately, so
normalized resolution refuses a selector naming it. The
[project selector rules](../language/projects.md#names-observations-and-queries) writes
such a selector out as the member functions that carry the site before
resolution. Ordinary function selectors bind directly to their emitted symbols,
including imported functions that also have qualified logical origins.
A concrete name can also be a legitimate logical origin of other functions,
including ordinary helper specializations. Before translating a selected label,
each reader checks the whole alias family in both directions: all matching raw
occurrences must map to the selected coordinate, and every occurrence at that
coordinate must carry the selected raw label. Disagreement refuses only the
normalized construction (`construction-selector-coordinates`). It does not
refuse source admission or exact construction. This guards against selecting an
unrelated draw merely because independent function counters both produced
`site0`. Whole family maps need not be identical, only selected membership.
The owner's site supplies the coordinate; it need not itself be a primitive
when another function in that origin family supplies the selected draw.
Construction checks the actual selected primitives after helper expansion.

C++ construction consumes the resolved source and descriptor but hashes the
original source into generated names and returns the original descriptor in the
construction result. Rust derives its own resolved source before requesting the
existing preparation view; controls must equal that resolved original, and
prepared functions/bindings must occur in the checked construction result.
Lean independently resolves original source, descriptor and configuration before
its original-source reference execution. No backend event hook or change to
runtime frame custody is needed. The existing origin encoding remains `/1`:
its fields still identify source occurrences, now in the normalized construction's
explicitly selected resolved source. The descriptor's identity policy separates
this contract from exact identity inside the binding root.

## Normalized protocol representation

Rust and Lean independently derive the following string/array tree from the
original admitted source (generic form, without native specialization):

```text
["zkc.protocol-identity/1", entryRecord,
 sortedInstances, sortedProtocols, sortedFunctions,
 sortedGenericDefinitions, sortedFlattenedConfigurations]
```

Select the descriptor entry. Include its root instance and every instance in
their declared dependency maps, recursively. Include their protocol definitions
and transitive declared protocol dependencies, their complete bodies (including
zero-trip loops, guards, unused results and resource operations), every local
callee in these bodies, and the generic definitions of selected configurations.
Only demanded configurations appear, flattened to their final definition with
arguments in definition-parameter order and an empty implementation-selection
list. A partial configuration chain is resolved without specializing its body;
all demanded arguments must be present. All admission checks still cover the
entire original library, including excluded declarations and choices.

Sort each top-level declaration group by retained declaration name (UTF-8 byte
order). Retain instance records, protocol roles/parameters/ports/results and
dependency declarations exactly. Normalize complete bodies as follows:

* Replace sites with the declaration's `siteN` coordinates.
* Replace local SSA binders and references with `v0`, `v1`, ... in binding order.
  A function's inputs establish its initial environment. A protocol's public
  port declarations keep their names, but its body refers to their ordinal
  `vN` entries. Loop carried values and captures resolve in the outer scope;
  their body binders establish a fresh inner environment, followed by nested
  results. Outer loop results are bound only after the nested body. Preserve
  all list orders and operation attributes.
  Executable source captures are strings; the normalized identity alone expands
  each capture to `[innerBinder, outerReference]`. This makes the two scopes
  explicit. The identity tree is not an executable common-source carrier.
* In ordinary function operations, replace the binding symbol with
  `["operation", contract, staticArguments]` from its declaration. Omit that
  binding's implementation choice. Keep any explicit function-origin record;
  it is an authority-bearing declaration, not a debug alias.
* Keep generic operation contracts, static terms and predicates verbatim, apart
  from site/SSA resolution. Do not prove identities of static expressions or
  canonicalize equivalent field literals. Generic parameter names remain part
  of this bounded contract.

The root is the existing canonical string/array encoding of:

```text
["zkc.artifact-binding/1", normalizedProtocol,
 resolvedDescriptor, applicationContextHex, publicRecords,
 resolvedApplicationConfiguration]
```

Public records retain the existing declaration order and canonical encoding.
The application configuration retains all authorized key bytes, registry names,
assignments and ordering, changing only receive-site aliases to coordinates.
Private witness values remain excluded. Merlin's installed suite and event
encoding do not change; domain separation includes the selected binding root.

This promises label/local-SSA/binding-alias and physical-choice independence,
top-level declaration permutation, and exclusion of unrelated valid declarations.
It does not promise invariance under arbitrary algebraic rewrites, reordered
operations, renamed public interfaces, parameter renaming, different configuration
names, changed codecs, or a different cryptographic construction.

## Selection, diagnosis and assurance

The authoring frontend may omit an instruction label. Its declaration-scoped
`__site_N` names reserve all explicit labels, including later and nested ones.
These are source aliases; normalized resolution above determines transcript sites.
Names of declarations, configurations, roles, public ports and schemas are not
cosmetic under this contract. A source location or generated MLIR symbol does
not authorize an occurrence or supply evidence of its meaning.

Compiler implementation selections are separate. A
`["zkc.implementation-selection/1", snapshot, selections]` envelope requires the
SHA-256 of UTF-8 `zkc.source-snapshot/1\n` followed by `printJson(originalSource)`.
It is checked before elaboration. Formatting and source spans are absent from
that serialization; changed source records invalidate the snapshot. Unqualified
binding/implementation pairs, without the envelope, are accepted without that
freshness claim. Neither selection envelope nor source snapshot enters `zkc.artifact-binding/1`.
A source hash is neither a hiding commitment nor authentication.

The runtime uses installed implementations of admitted mathematical and wire
contracts. Omitting physical selections from protocol identity does not prove
that two implementations satisfy those contracts. The current finite registry
and backend assumptions remain part of execution assurance. Changing a
mathematical identity, wire codec or cryptographic construction requires its own
explicit contract; it is not an implementation-only rewrite.

Rust's `inspect-artifact-identity SOURCE DESCRIPTOR [CONFIGURATION]` exposes a
bounded structural derivation and reports `admission: "not-checked"`. Lean's
`artifact-reference identity SOURCE DESCRIPTOR [CONFIGURATION]` independently
checks the source/artifact profile and returns its resolved and normalized trees.
Neither inspection substitutes for source/candidate admission on execution.

[Typed conditional laws](../../formal/Tools/Artifact/Identity/Laws.lean) preserve
execution under an explicitly shared interpretation and corresponding typed
environments; representation laws retain operation contracts and dynamic
ancestry. They do not prove raw JSON normalization adequate for that typed
semantics. Native/Lean tree and actual execution comparisons are differential
evidence with retained original inputs. The native constructor, byte parsers,
cryptographic adapters and raw-to-typed connection retain their stated trust
boundaries.

## Compiled relation snapshots

`zkc.relations/1` is not an additional source accepted by `zkc.artifact-binding/1`.
Identity readers must refuse it rather than hash only its nested protocol.
`protocol-materialize` is an explicit native lowering to ordinary source;
its generated function origins and matrix-content checks remain in that source.
Applications must preserve the original relation association across this
boundary. The separate noninteractive Groth16 host includes the resolved exact
relation identity, expected full verification key and statement in its invocation
binding. This does not extend Fiat–Shamir normalization or prove the correctness
of relation materialization or setup. See [relation authoring](../language/relations.md).
