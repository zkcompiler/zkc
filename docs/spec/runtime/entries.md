# Entry admission and calls

This is a native contract. See the [language contract index](../language/README.md)
for source rules and the [runtime reference](../../runtime/README.md) for usage.

## Rust interface admission

The native Host reads `zkc.language-interface/0`. It checks strict object members,
including required nullable fields, before using source names. Recursive schema
validation preserves kind, exact logical identity, permissions, custody, field
slices and nominal alternatives. Every logical port remains present, including
zero-leaf values. Selectors and Entry choices must agree with those schemas.

Compiler publication and both readers bound interface bytes at 4 MiB, JSON
nesting at 256 and lexical nodes
at 200,000 before typed decoding. Scalar tokens have at most ten bytes; encoded
string tokens have at most six times 256 KiB. Decoded strings retain their owning
name/type limits. Schema depth is at most 32, each aggregate has at most 1,024
leaves, and validation has a cumulative work allowance of 1,000,000. Native leaf
parsing retains its own structural bounds; cached descriptors have an additional
16 MiB total retained charge. Work bounds apply independently to each admission
algorithm; a caller may also lower the compiler's phase limits. Unknown and
duplicate fields refuse. The bounded tree format retains self-contained schemas;
identities permit descriptor reuse without introducing cyclic schema references.

Native binding checks the exact artifact bytes from the authenticated package,
selected entry, participant roster, logical data types, services and output
mappings. Proof binding additionally checks the original digest, original
acceptance port, public inputs, construction and compile options against the
admitted deployment. Run bundles carry no independent original/options record;
those choices are authenticated package metadata. The compiler/checker publication
path owns source correspondence and relation meaning. Reading metadata or binding
its ports does not interpret MLIR or establish a protocol security judgment.

## Named setup authority and initialization

Named setup associations instantiate the [setup registry contract](../formats/messages.md#application-authorized-setups).

Both source Hosts accept `entry::SetupAuthority`, whose `keys` map covers setup
slot names exactly and supplies independently authorized verifier-key identities.
Unknown or missing names refuse with `entry-setup-authority`. The adapter derives
native maps from the authenticated interface: run maps use role-local operand
indices; proof maps pin every original public verifier-key index and associate
other setup-bearing inputs with the slot's lowest verifier-key index. Native
admission independently checks complete coverage and concrete types.

The source Host derives one immutable port plan from the checked interface. It
records role order, public/private inputs, setup-key ports, selected outputs and
external services. Generated bindings, file requests and native ABI comparison
use that plan. Native artifact facts are read independently during comparison.

`RunRequest::setups` and `ProofRequest::setups` supply verifier-key bytes for every
slot exactly. The Host authenticates and imports them through its existing bounded
setup loader. Whole verifier-key inputs are initialized automatically: applications
omit them from both named role inputs and named public values. Supplying a second
value under that port name refuses. Prover-key inputs remain explicit named
`Value::Leaf` values containing authenticated `ProverMaterial` or a
`ProverKeyFile` with an independently expected material fingerprint. Other
constructors, including arbitrary native key values, refuse.

Each invocation checks prover material against its assigned slot. Immutable
material may be reused across calls; runtime accounting and setup checks still
apply per call. Names and byte/copy limits are checked before constructing public
key input vectors. Native input admission owns key parsing, canonical bytes,
setup metadata checks and execution budgets. This does not establish honest setup
generation or authorize a private source representation.

## Named run calls

Rust `entry::RunEntry::admit` retains an authenticated package, validates its
interface and admits the exact run artifact through `RunHost`. Proof jobs use a
separate API. Before accepting a run, every logical output must be copyable and
have no affine custody; unsupported custody returns `entry-output-custody`.
Every ordinary input must have source `Wire` constructor permission or admission
returns `entry-input-constructor`. Whole builtin key ports instead use the explicit
setup route above. These checks precede native bundle admission.

`RunRequest` names every participant and its ordinary/prover-key input ports
exactly. Its service map supplies optional budget overrides for declared services;
unknown names refuse. Each role remains required even when it has no inputs. Unit values and empty
products also remain explicit. Records use exact field names, tuples and arrays
use ordered elements, variants name an active alternative and its payload fields,
and associated values wrap their checked representation. Numeric alternative
field names follow the declared payload order. The checked schema supplies all
native slices and nominal descriptors; display type strings are not executable
layout descriptions.

Ordinary leaves use `entry::Value::Leaf(InputValue::Native(...))` or `Wire`.
The admitted source schema's `Wire` constructor permission applies recursively
through products and alternative payloads. A matching native representation does
not confer private constructor authority. Source randomness comes through named
managed services; setup keys use the named initialization route above. Native
leaves retain the upstream cryptographic library invariants stated
by the run Host. Variant payloads can mix native and wire data; common admission
checks complete types, aggregate collection counts and retention before decoding
or constructing payload containers.

`prepare` consumes the named request and returns a single-use plan backed by the
same native Host. `execute` retains the complete native outcome, usage and cleanup
report. On complete execution with successful cleanup, it reconstructs all named
results, including empty products. Other outcomes publish no complete logical
result; they remain visible in the native report. An unexpected reconstruction
failure has its own `output_error` and cannot become successful named output.
`RunReport::is_success` checks completion, successful cleanup and decoded outputs;
`into_result` preserves the full report on either branch. A successful interactive
run does not imply a protocol acceptance predicate: the caller must inspect its
explicit result values. No source evaluation or protocol-specific execution loop
is added.

## Named proof calls

`entry::ProofEntry::admit` authenticates the same package/interface boundary and
binds the exact deployment through `NativeDeployment`. Inputs retain the source
constructor requirement and outputs must be copyable without affine custody.
`prove` and `verify` take separate `ProofRequest` values; the verifier receives
only its own inputs and the candidate proof. Neither method needs a live peer.
The SDK supplies public values once through `ProofRequest::public`; `private`
contains only nonpublic inputs and external service budgets. The source adapter
assembles shared operands from these public values. Private overrides refuse;
native admission still checks canonical agreement. Setup imports may reuse
identical canonical bytes under the same authorized pin within an invocation;
each native operand retains its usual resource charge.

Each request also supplies application context bytes and an optional transcript
budget. Public values remain independently authorized by the application.
Zero-leaf public and private inputs remain required in their respective maps.
The selected derived verifier service is compiler-owned and cannot also appear
in the caller's service map. Products and nominal alternatives use the same
logical schema and common admission as run calls.

`ProofOptions::binding` defaults to `TranscriptRequired`. Authored construction
requires explicit `AllowHeaderOnly`; otherwise admission returns
`entry-proof-binding-policy`. `binding_scope()` and each `ProofReport` distinguish
`Transcript` from `HeaderOnly`. This identifies the selected binding mechanism,
not a cryptographic security judgment. The authored header checks consistency;
it does not by itself prevent rewrapping a proof under another context.

A successful `ProofReport` reconstructs that participant's named original
outputs, including empty products. Rejection, stop, refusal or cleanup failure
publishes no named outputs; the native outcome, usage and cleanup remain visible.
Unexpected reconstruction failure is recorded in `output_error`. An outer `Ok`
means preparation succeeded, not proof acceptance. The report is `must_use`;
`is_success()` checks execution, cleanup and output reconstruction together.
`into_result()` returns the entire report on either branch, preserving rejection
and cleanup details.

## Attempts and operational defaults

Entry attempts specialize the [native attempt policy](attempts.md) under the
source ingress restriction below.

When completion is selected, `prove(request)` delegates to the native attempt
controller with a one-attempt limit. A false completion withholds proof bytes and
returns `native-attempt-limit`; it does not authorize another attempt.
`prove_attempts(request, AttemptOptions)` requires the Entry's `complete` choice,
otherwise it refuses with `entry-attempt-completion`. The adapter resolves that
logical selector to its checked original native output and delegates to the
existing attempt controller. `AttemptOptions` supplies count (default one) and
per-attempt proof-byte ceiling (default the native proof limit). The admitted
`ProofOptions::capacity` supplies cumulative interpreter work and payload limits;
external work keeps its existing Host ceiling. Native policy admission checks all
limits before loading resources. No raw native port policy is needed in the
source API; direct IR callers retain the native API.

The authenticated Entry interface and independent source comparison own the
completion selection. It is an application policy, so the native artifact does
not repeat that selection. Native attempt-policy admission checks that the
selected original output maps to a prover Boolean output; the controller uses
its actual result to decide whether to publish a proof.

Managed providers persist across attempts with their actual remaining allowances.
A false completion discards its proof buffer; fatal stops and cleanup failures do
not become retries. Only final successful outputs are published. The source
profile has no affine RNG input constructors; the native policy therefore has no
RNG input/successor pairs. Extending that ingress needs its own custody mapping.
Neither the final proof nor the policy digest establishes the retry distribution.

An omitted declared service budget uses `entry::DEFAULT_DRAW_BUDGET` (1,000,000),
the current native admission ceiling. `ProofRequest::transcript_budget` is optional:
omission uses that allowance for derived construction and zero for authored jobs.
Explicit values, including zero, override defaults. A nonzero explicit transcript
budget for an authored job still refuses. Unknown service names and attempts to
supply the compiler-owned derived service still refuse.

These are operational allowances, not inferred draw counts. They allocate no
random tape and confer no independence or honest-provider claim. Existing native
resource/transcript observations report consumed transitions and remaining
allowances. Provider budgets persist for the whole invocation; each derived
attempt transcript starts its separately bounded allowance. Callers can lower
budgets and native hard limits still apply.

## File adapters and Rust bindings

The CLI and generated bindings use the same named Hosts. `zkc compile` invokes
a compiler selected by an explicit path or absolute directories in the caller's
trusted `PATH` (default
`zkc-compile`), reports its resolved path and toolchain, captures its
bounded package output and publishes exact bytes with their SHA-256. Existing
packages require a caller-supplied expected digest for `run`, `prove`,
`verify` and `bindings`. No digest derived from candidate bytes authorizes them.

A `zkc.entry-run/0` request has required `format`, `session` and `roles`, plus
optional `setups` (default empty). Every role record has required `inputs` and
optional `services` (default no overrides). A `zkc.entry-proof/0` request has
required `format` and `public`, plus optional `inputs` (private value map,
default empty), `services` (default no overrides), `context` (default empty hex), `transcript_budget` (default absent) and `setups`
(default empty). Public and input maps use exact logical port names. The file
adapter fills shared role operands from `public`; `inputs` cannot repeat or
override public names. Independent callers still provide their own public maps. Setup
material maps slot names to canonical verifier-key bytes in hex. Whole VK ports
are omitted from value maps. A whole prover-key port supplies exactly `path`
and `sha256`; key paths resolve from the invoking process working directory.

Values use Boolean JSON for Boolean source values, unsigned 64-bit integers for
indices, null for unit, arrays for tuples/fixed arrays, and exact named objects
for records. A variant has exactly `case` (the alternative name) and `fields`
(a named object, including numeric field names for positional payloads).
Associated representations are transparent. Installed mathematical leaves use
hex of their complete canonical native wire frame. Native decoding retains its
exact type, canonicality, setup and quota checks. Typed Rust ingress avoids this
file encoding and retains its independent immutable-value validation.

The optional application authority file contains exactly
`format: "zkc.entry-setups/0"` and `keys`, mapping source slots to expected
32-byte key identities in hex. Authority is separate from invocation material.

[File admission and publication](publication.md) defines request limits,
regular-file and path checks, output formats, staging, replacement, diagnostics
and success status.

Generated Rust modules pin the exact package digest and delegate admission to the
common Host. They provide named participant/public input and output structures,
structural value conversions, and Rust representations of Boolean/index/unit,
array and nominal data. Mathematical leaves remain `entry::Value`, with concrete
domain and authority validation at invocation. Identifier conversion avoids Rust
keywords and collisions while retaining original source keys in conversions.
Field and variant names retain exact source spelling. Reserved path names, `_`
and names beginning `__zkc_` use that prefix followed by hex of the full source
identifier. Generated naming-lint allowances cover these intentional spellings;
they do not disable general warnings. Fixed public-interface names are allocated
before source-derived names. Role conversion helpers and name constants delegate
to the same request/result maps.
Bindings emit no protocol algorithm or new execution/authority implementation.
Generated source is bounded by 16 MiB. Reauthorizing a different package requires
regenerating or deliberately replacing its pin.

## Error phases

Calls that fail before execution return `EntryError`, whose `phase` identifies
package authentication, interface reading, setup authority, native admission,
interface binding, request conversion or native preparation. Phases identify
where rejection occurred; `code()` identifies the reason. For example, an unknown
input name fails at `Request`, while an invalid native context or resource budget
fails at `Preparation`. Native preparation can also reject malformed input values.
Execution failures and cleanup remain in the report.
