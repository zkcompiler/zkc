# Native public-coin views

This profile selects a bounded structural analysis of the
[native mathematical protocol](protocols.md). It uses the existing
`protocol → participant → exec → physical` route. It adds no operation, IR
stage, random-oracle interpretation or cryptographic transformation.

## Judgment

Given an admitted common source, an independently supplied requirement and a
selected verifier V, establish this sufficient fact on an **expanded,
unsimplified** copy of its entry:

> V's guard conditions and selected Boolean decision depend only on its bound
> entry components, its actual receives, and its designated service draws. Every
> draw has exactly one unchanged delivery to P before another draw or V receive.

Dependence is syntactic and conservative. Constants have empty dependence;
total expressions union the dependence of their operands, using the registered
operation contract. Restriction preserves the selected component. At P→V
exchange, **V's receive is a fresh anchor**: the analysis does not follow the
sent expression. At V→P exchange, V retains its own sent component. This
respects role-family semantics; availability at P and V does not imply equality.

All statement operands selected at V must also be bound. These include witness
operands if a declaration explicitly selects them. The report separately marks
bound inputs that lack a V-selected `parameter` or `statement` purpose.
Declarations referring to other output indices do not change the selected
Boolean decision or establish that it decides those relations.

A source refusal establishes neither insecurity nor algebraic independence.
For example, syntactic dependence on `x` in `x == x` is retained. The judgment
concerns guard conditions and a selected returned decision on reached prefixes;
it does not characterize termination, scheduling, other returned values, or
prover local behavior. A stopped guard is distinct from a returned `false`.

## Requirement and accepted fragment

`zkc.public-coin-requirement/0` is an exact JSON object:

```json
{
  "format": "zkc.public-coin-requirement/0",
  "entry": "main",
  "prover": "Prover",
  "verifier": "Checker",
  "service": 1,
  "decision": 0,
  "bound_inputs": [0],
  "draws": [
    {"query_site": "draw", "delivery_site": "coin"}
  ]
}
```

Numeric values use unsigned integer tokens; signs, leading zeros, decimal points
and exponents are refused. Duplicate object keys, including differently escaped
spellings of the same key, are refused. Unicode escapes must denote scalar
values; unpaired UTF-16 surrogates are refused. Input/result indices address the
common entry interface. `bound_inputs` is an
ordered, duplicate-free list; it may be empty. Each selected input must have a
V component and an admitted native wire type. Binding here declares the view's
initial values, not a runtime authentication mechanism or a hash operation.
V-only bound inputs are accepted and explicitly reported as unavailable at P.

The entry has exactly the two distinct specified roles. Its selected result is
Boolean and available at V. The designated service is an exclusively V-owned
installed [random-service](../runtime/services.md) entry port. Every query in the expanded entry uses that
port and uses `draw`; other methods, including `index`, refuse with
`public-coin-service`. Query sites equal the requirement's list in source order;
ordinary native admission checks each method's signature. There is at least one
query. This field-draw profile does not describe UniformIndex distributions.

Every V→P exchange is the unique designated delivery of the pending draw. Its
operand must be that query's result, optionally through `restrict_roles`.
Arithmetic equivalence is insufficient. Delivery precedes the next query or
P→V receive, and all queries must be delivered before return. Multiple
outstanding draws are outside this profile. P→V messages need no syntactic
relationship to the declared prover expression. V-owned local calls are
refused, including calls with no outputs: they can hide state or stopping.
P-owned local calls and guards retain their ordinary meaning. V guards may
intervene between a draw and delivery; their prefixes include the draw although
P has not received it yet. Statement bindings belong to the entry; ordinary
static application admission refuses a callee that contains a statement.

## Derived report and checking

`zkc.public-coin-view/0` contains:

- The entry, roles, service and decision indices.
- `anchors`: input entries in original port order, then actual V receives and
  draws in action order. Input anchors include unused/unbound ports; only
  declared bound inputs enter the view. Input anchors have `port` and `type`;
  receive/draw anchors have `site`, authored `path`, `kind` and `type`.
- `events`: anchor indices, beginning with `bound_inputs` in requirement order,
  followed by receives and draws in source order.
- `draws`: query `site`, authored `path`, `prefix_length` into `events`, and the
  matched delivery's `site` and `path`. The prefix excludes this draw and all
  later events. It is conditional on reaching the query.
- `guards`: V guard site/path, current prefix length and dependency anchor
  indices. `decision_dependencies` lists the selected decision's anchors.
- `statement_inputs`, `bound_non_statement_inputs`, and
  `prover_unavailable_bound_inputs`, each in increasing port order.
- `source_ir_sha256`, `prepared_ir_sha256`, and `requirement_sha256`.
  The prepared identity uses the source analysis view with default preparation;
  it does not identify a separately fused compilation candidate.

IR identities hash the default MLIR printing of the admitted original module
and unsimplified prepared module; locations are omitted. The requirement hash
covers the exact supplied JSON bytes. Hashes identify artifacts, not proofs.
Each authored action path is the sequence of application sites followed by the
leaf action site; the entry is retained separately. Expanded names follow the
existing length-prefixed application convention. Neither naming scheme is
adopted as cryptographic domain separation. Renaming requires recomputation. Printer/preparation changes can also change
these identities: reports are specific to the compiler and MLIR version, not a
cross-version canonical encoding.

`analyzePublicCoin` leaves its original module unchanged and owns all returned
report data after its prepared copy is destroyed. `checkPublicCoin` recomputes
the whole report from the original and the independent requirement, then
compares JSON values exactly after checking integer tokens, Unicode escapes and
key uniqueness. Whitespace and object-key order are immaterial; floating-point
spellings are not accepted. No supplied report fact is trusted; additional keys
are refused too. Neither API checks an arbitrary transformed program.

## Checked compilation

`RunOptions.publicCoinRequirement` requests this analysis before
projection. Its entry must equal the compiled entry. Ordinary projection,
simplification and lowering remain trusted/tested compiler passes.
`CompiledRun.publicCoin` returns `zkc.compiled-public-coin/0`, containing
`view`, exact input-text `source_sha256`, emitted `bundle_sha256`, and the
`simplify`, `release_storage`, `fuse_vector_reductions`, `fix_polynomial_factors`
options, the actual `projection_simplify` setting and ordered
`post_analysis_passes`. The compiler
returns no partial executable on failure.

`fuse_vector_reductions` defaults to false and records the selected
[local preparation rewrite](protocols.md#optional-vector-reduction-fusion).
The standalone public-coin view remains an analysis of its own unsimplified
prepared subject. The compiled report lists `zkc-prepare-protocol` before
projection in `post_analysis_passes`, because optional fusion occurs there.
It is independent of participant simplification and storage release. Polynomial
correspondence compilation and `checkPolynomialReductions` forward the same
preparation choice and record `fuse_vector_reductions` in the correspondence
report. `protocol-check-reductions` accepts the matching option for comparison
with a supplied candidate. A report does not make local fusion a Fiat–Shamir
reduction or general resource-preservation theorem.

The CLI supports:

```sh
zkc-compile protocol-public-coin source.mlir requirement.json
zkc-compile protocol-check-public-coin source.mlir requirement.json view.json
zkc-compile protocol-checked-bundle source.mlir --public-coin=requirement.json
```

Successful report checking prints `{"format":"zkc.public-coin-checked/0"}`.
Checked compilation with a public-coin requirement emits
`zkc.checked-run/0`: `bundle`, `public_coin`, and `correspondence` (null
unless `--requirements` also requests polynomial correspondence). Polynomial-only
compilation uses the same wrapper with `public_coin` set to null. For later report
checking, supply the inner `view`, not the compiled wrapper.

## Bounds and refusals

Requirements are at most 1 MiB, JSON nesting 64, names 4096 bytes, input/result
indices below 1024, at most 1024 bound ports and 1–64 draws. Sites and input
indices are unique. Source and prepared fingerprints are bounded at 16 MiB
of default printed IR. Ordinary module admission and preparation budgets apply
first. The entry has at most 1024 inputs/results and 2048 action occurrences;
authored occurrence paths plus expanded names occupy at most 1 MiB. The analysis
allocates a dependency bit vector per V-available SSA value. It charges
`ceil(number_of_anchors / 64) + 1` units per stored vector and operand union,
with a total budget of 1,000,000. At most 65,536 dependency indices are emitted.
Candidate reports are bounded at 8 MiB and JSON nesting 64 before parsing.
The CLI additionally bounds source text at 16 MiB before MLIR parsing.

`public-coin-requirement` rejects the requirement schema; `public-coin-interface`
rejects entry/role/port selection; `public-coin-service`,
`public-coin-delivery`, `public-coin-verifier-local`, `public-coin-statement`,
and `public-coin-unbound-input` identify failed fragment conditions.
`public-coin-limit` rejects a resource bound. `public-coin-module` reports
ordinary admission/preparation failure, `public-coin-occurrence` an inconsistent
authored path, and `public-coin-dependence` an unavailable dependence contract.
Conditional entry completion (`protocol.finish_if`) lacks a total-verifier
dependence contract and is refused as `public-coin-dependence`.
`public-coin-report` rejects a malformed or mismatched candidate report;
`public-coin-options` rejects standalone CLI arity.
`checked-bundle-requirement-missing` rejects checked compilation without either
independent requirement.

## Security and formal boundary

Verifier-view analysis and [native transcript construction](../formats/proof.md)
have distinct contracts. The view fact supplies no freshness/uniformity law,
P/V agreement premise, hash codec or application domain,
Fiat–Shamir security, round-by-round soundness, algebraic completeness or special
soundness theorem. Concrete service failure, wire decoding, cancellation and
resource exhaustion retain the native runtime's outcomes. Trace tests compare
draw prefixes on the generated fixtures with their execution; no new Lean
correspondence is claimed.
