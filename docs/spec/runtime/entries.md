# Entry admission and calls

This is a native contract. See the [language contract index](../language/README.md)
for source rules and the [runtime reference](../../runtime/README.md) for usage.

## Rust interface admission

The native Host reads `zkc.language-interface/0`. It checks strict object members,
including required nullable fields, before using source names. Recursive schema
validation preserves kind, exact logical identity, permissions, custody, field
slices and nominal alternatives. Every logical port remains present, including
zero-leaf values. Selectors and Entry choices must agree with those schemas.
Source names use the [Unicode source profile](../language/lexical.md), retaining
exact NFC UTF-8 bytes. Raw UTF-8 and equivalent valid JSON escapes decode to the
same names; invalid UTF-8, lone surrogates and duplicate decoded keys refuse.
Native role/setup/case labels are derived only from authenticated ordered rosters
using the [source/native encoding](../language/translation.md#source-and-native-names).
Binding compares these derived ordinals against the actual artifact, including
ASCII source names. Logical names are never interpreted as preexisting native IDs.
Variant nominal identities decode bounded canonical lowercase hex of the complete
UTF-8 type-key preimage and check its digest; a label or digest alone is insufficient.

`Interface` is this checked logical view, also available from source inspection
before executable lowering. `BoundInterface` adds authenticated package identity
and compile options; only that bound view can bind a native deployment.

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
Unknown or missing names refuse with `entry-setup-authority`. Both authority
keys and request material keys use source slot names. The adapter translates both
through the same roster to `setup` plus eight lowercase hexadecimal digits,
starting at `setup00000000`. Translating only one map is insufficient. It derives
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
`Value::Leaf` values containing authenticated `ProverMaterial`, a `ProverKeyFile`
path, or a descriptor-backed `ProverKeyInput`. Both file forms require an
independently expected material fingerprint. Other
constructors, including arbitrary native key values, refuse.

Each invocation checks prover material against its assigned slot. Immutable
material may be reused across calls; runtime accounting and setup checks still
apply per call. Names and byte/copy limits are checked before constructing public
key input vectors. Native input admission owns key parsing, canonical bytes,
setup metadata checks and execution budgets. This does not establish honest setup
generation or authorize a private source representation.

## Packaged expression assets

Both named Hosts take their ring arenas and relation Bundles from the authenticated package's
[`assets` member](../formats/entry.md#published-entry-package) and from nowhere
else. After native admission and interface binding, `RunEntry::admit` and
`ProofEntry::admit` admit every packaged body through its independent ring or
Bundle reader and backend registry, with their formation, identity, per-item and
aggregate limits. Registry refusals pass through unchanged, for example
`refused:ring-asset-identity` when a body does not hash to its expected
digest. The retained body must also be byte-identical to the admitted
expression's canonical encoding, or admission returns `entry-asset-canonical`:
a package carries one representation per asset.

The Host then checks the admitted native program's references against those
assets. It walks the entry's participants, their nested loop bodies, every
function they call, and every local region of those functions, including
branches no execution chooses and loop bodies zero trips never enter. The
walk uses the admitted typed program; it does not scan artifact text. Each
operation whose binding carries an asset identity attribute is a reference.
For `ring.point`, `ring.rows`, `ring.coefficients` and `ring.affine_sum` the
carrier is the field of the operation's first vector operand, taken from the
admitted signature. The referenced arena must be admitted, else
`entry-asset-missing`, and its inputs and facts must be interpretable in that
carrier under the kernels' own rule, else `entry-asset-carrier`: KoalaBear
arenas under an Ext8 carrier are permitted, the converse is not.
For `relation.table_rows`, the Host checks the selected static table index and
the Bundle view's exact field requirements. It does not promote a base-field
trace to arbitrary extension-field values. For `relation.table_shape`,
`relation.table_input`, `relation.table_scope`, `relation.table_point` and
`relation.table_points`, the carrier is the binding's field argument. These
contracts share one rule, checked once per asset, table and carrier without
allocating: the static table index, the
[polynomial view's](../domains/relation-bundles.md#compiler-visible-polynomial-view)
carrier rule, which lets a KoalaBear table be substituted in Ext8, and that
the height policy admits a power of two of at least 2. The
[interaction view's](../domains/relation-bundles.md#compiler-visible-interaction-view)
`relation.table_interactions`, `relation.table_interaction` and
`relation.table_record_points`, together with `relation.table_policy`, share
a second rule: the static table index and the whole-table carrier rule,
which also visits every interaction output. None requires a polynomial
domain or power-of-two height at reference admission. Height-taking kernels
check their own height policies and windows at execution. A polynomial
reference whose table admits no supported two-adic height is refused at Host
admission with `refused:bundle-polynomial-two-adic`. A Bundle relation declaration also
requires its packaged body; the Host independently checks its derived formal
ABI, returning `entry-asset-relation` on disagreement. An operation
of another asset-naming contract returns `entry-asset-contract`. These checks
complete before any request is converted or any input, key or resource is
issued; a missing or incompatible asset is never deferred to execution. An
admitted asset that no reachable operation references is retained and
reported, not refused.

The admitted registries are installed into the Entry's native run or proof Host
before the Entry is returned. `RunEntry::assets` and `ProofEntry::assets`
expose them as `EntryAssets`: admitted identities, each admitted expression or Bundle, the
checked references with their function, site, binding and identity, and the
registries themselves. No `RunEntry` or `ProofEntry` method accepts a caller-supplied
registry, so an application cannot replace or extend the packaged assets on the
authenticated path. The native `RunHost`, `NativeDeployment` and backend
registry constructors keep their explicit registry route for direct native
programs. Asset admission establishes content identity and static reference
coverage; it is not a judgment about an arena's meaning in the protocol.

## Named run calls

Rust `entry::RunEntry::admit` retains an authenticated package, validates its
interface and admits the exact run artifact through `RunHost`. Proof jobs use a
separate API. Before accepting a run, every logical output must be copyable and
have no affine custody; unsupported custody returns `entry-output-custody`.
Every ordinary input must have source `Wire` constructor permission or admission
returns `entry-input-constructor`. Whole builtin key ports instead use the explicit
setup route above. These checks precede native bundle admission, which precedes
asset admission.

`RunRequest` names every participant and its ordinary/prover-key input ports
exactly. Its service map supplies optional budget overrides for declared services;
unknown names refuse. Each role remains required even when it has no inputs. Unit values and empty
products also remain explicit. Records use exact field names, tuples and arrays
use ordered elements, variants name an active alternative and its payload fields,
and associated values wrap their checked representation. Numeric alternative
field names follow the declared payload order. The checked schema supplies all
native slices and nominal descriptors; display type strings are not executable
layout descriptions.

Ordinary leaves use `entry::Value::Leaf` with `InputValue::Native`, `Wire`, or
`WireFile`. `WireFile` retains an opened regular descriptor and an expected
SHA-256; common Host preparation reads and authenticates it under input limits.
The admitted source schema's `Wire` constructor permission applies recursively
through products and alternative payloads. A matching native representation does
not confer private constructor authority. Source randomness comes through named
managed services; setup keys use the named initialization route above. Native
leaves retain the upstream cryptographic library invariants stated
by the run Host. Variant payloads can mix native and wire data; common admission
checks complete types, aggregate collection counts and retention before decoding
or constructing payload containers.

`prepare` consumes the named request and returns a single-use plan backed by the
same native Host, before any resource issuance. `check_inputs` applies that
preparation and discards the unexecuted plan. `execute` retains the complete native outcome, usage and cleanup
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

The CLI and generated bindings use the same named Hosts. The public
`project::{Project, Compiler, Selection}` API owns project resolution and bounded
compiler invocation. A compiler is selected explicitly or through absolute
directories in trusted `PATH`. Source execution compiles in memory, captures the
exact returned package bytes, and reports their identity and compiler provenance.
`compile` additionally publishes those bytes. Existing packages require the
pair `--package=FILE --sha256=EXPECTED`; this mode refuses source options and
Entry positionals. A digest derived from candidate bytes never authorizes them.

Omitted Entry names select the unique eligible Entry. Run commands filter to
run Entries; prove/verify commands filter to proof Entries. Other commands
consider both kinds. Explicit short names must be unique across kinds before
checking eligibility. Qualified names resolve exactly. `inputs check` requires
`--operation=run|prove|verify` and uses that operation's eligibility and input rules.

`Interface` is the checked logical source view. `BoundInterface` additionally
binds it to the package's artifact identity and compile options. `inspect` and `inputs init`
can obtain the logical view directly from `language-interface`, before executable
lowering. Package inspection validates the captured package view. Neither path
performs native admission, key import, resource issuance or execution.
`zkc.entry-inspection/0` reports Entry/protocol/toolchain, role ports, services,
setup names, proof selections and input group schemas. Input schemas are derived
from that same checked Interface, not a separately persisted authority. Each
input reports whether its source permission and installed native representation
allow construction. This descriptive flag does not replace native admission.

Command help and syntax admission share one declaration. Options use
`--name=value` or bare switches; repeated single-use options refuse. A global
`--json` and one command-level `--json` select the same output mode. `--` ends
option parsing. Syntax errors return `cli-usage` or `cli-option` before file
access. `--json`, either before or after the command, selects a structured report
on standard output. Otherwise successful summaries use standard output and
refusals use standard error. Recognized-command refusals exit 1; missing or unknown
commands exit 2. Help/version remain text and exit 0 without input access. Successful execution
requires the complete outcome, including acceptance when applicable.

### Project defaults

`Project::layout()` owns manifest-relative paths. A canonical `a::B` Entry maps
to `a.B`, retaining exact NFC source spelling for Unicode names. Reserved device
names, overlong filenames and ASCII case-folded collisions refuse. The same checks
apply to input group filenames; explicit input paths bypass the filename convention. Explicit paths
override each input group or artifact independently and are relative to the
invocation's working directory. Package and explicit-module modes have no project
defaults. No command searches alternative filenames or selects a newest file.

- Required proof groups use `inputs/<qualified.name>/public.json` and
  `witness.json`. Only proving selects witness inputs.
- Required run groups use `inputs/<qualified.name>/<Role>.json`.
- Compilation uses `build/zkc/<qualified.name>.zkpkg`.
- Proving writes and verification reads `build/zkc/<qualified.name>.zkproof`.
- Runs publish values to `build/zkc/<qualified.name>.results.json`. Proof
  commands publish named values only with explicit `--results`.

`run --no-results` disables result publication and conflicts with `--results`.
This option does not bypass native output custody checks. Requested output
codecs are checked before execution; value-dependent encoding bounds still apply.

Default output directories are created as needed. Explicit output parents must
exist. All resolved inputs, proofs, sources, reference descriptors and policy
files participate in the same output-alias checks, whether selected explicitly
or by convention. Missing or malformed selected files refuse without fallback.
`inputs check` selects the same input groups but no proof input or output paths.
CLI path resolution and output preflight use the `invocation` report phase,
after obtaining the selected interface and before native admission or execution.

Every CLI run without `--session` draws 16 bytes from operating-system randomness
and uses their lowercase hex spelling as its session. Failure to obtain randomness
returns `entry-session-random`. The resolved session is reported and supplied to
the Host once; explicit sessions remain unchanged. Typed `RunRequest` callers
continue to supply sessions themselves.

### Input documents

Input files are exact port-name maps. Proof commands take `--public=FILE` and,
for proving only, `--witness=FILE`. Public values initialize both participant
operands; witness maps cannot repeat public names. Independent verifiers provide
their own public map. Run commands optionally take `--session=LABEL` and repeat
`--input=ROLE=FILE`; shared source ports remain separate role-local values.
A group with no ports can omit its file. Unit and empty-product ports remain
required even though they have no native leaves. Unknown fields, roles and
repeated role files refuse. Verification rejects `--witness` before file access.

Booleans use JSON Boolean values; unit uses null; tuples and arrays use arrays;
records use exact field-name objects. Variants contain exactly `case` and `fields`,
with numeric names for positional fields. Associated representations are
transparent. Fields and indices use canonical unsigned decimal strings: zero is
`"0"`, other values have no leading zeros. Signs, fractions, exponents, numeric
JSON and out-of-range values refuse; there is no modular reduction.

The native codec supplies readable forms for installed mathematical leaves:
field/group vectors and index collections use arrays; KoalaBear Ext8 uses eight
ascending base-field coordinates, with a base-field string accepted as an
embedding. A sparse matrix has exactly `rows`, `columns` and `entries`; each
entry is `[row,column,coefficient]`, in the native canonical sparse order.
Group elements use `{"bytes":"lowercase-canonical-element-hex"}`. The explicit
fallback `{"wire":"lowercase-complete-native-frame-hex"}` remains type checked.
Sequences recursively use their element codec. These forms allocate bounded
wire bytes; the common Host performs native scanning, retention estimation,
canonical decoding, setup validation and cumulative work accounting. They do not
add constructors for nonimportable custody values or internal polynomial types.

A native leaf can instead contain exactly `file` and `sha256`. This authenticates
complete native-frame bytes. A whole prover-key input contains exactly `file`
and `fingerprint`, identifying canonical imported key material. Each document
gets its own parent directory capability. References are relative slash-separated
paths with no empty, dot, parent, backslash or NUL components. Every intermediate
directory and final regular file is opened without following symlinks. The Host
reads the retained descriptor under its existing wire/key and aggregate limits;
it never reopens the reference path. This resolver is supported on Unix; other
platforms refuse references. Explicit application resolvers are opt-in through
`entry::inputs::Resolver`; the pure decoder has no filesystem access by default.
Invocation JSON shares a 16 MiB byte limit, 200,000-node limit and depth limit 72;
references share a limit of 1,024; operating-system descriptor limits may refuse
earlier with `entry-input-descriptor-limit`. Excess reference count returns
`entry-input-reference-limit`; an oversized referenced value returns
`entry-input-reference-byte-limit`. Repeated paths within one document
share one retained descriptor. Missing or invalid document paths return
`entry-input-document`; reference digest mismatch returns `entry-input-reference-digest`.
Document byte, node and depth exhaustion return `entry-request-limit`.
Diagnostics name a logical input path when
readable decoding or reference resolution fails, without printing input values.

Whole verifier-key ports are omitted from maps and supplied via `--key=SLOT=FILE`.
Independent authority comes from `--setups=FILE`, containing exactly
`format: "zkc.entry-setups/0"` and a `keys` map of expected setup identities.
Service overrides use `--service=ROLE.NAME=COUNT`; context and transcript budget
use `--context=HEX` and `--transcript-budget=COUNT`. Options unsupported by an
operation refuse before input access. `inputs check` shares native input
preparation, including key authority and bounds, with execution. It executes no
protocol, issues no resources and parses no proof. It does not check satisfaction
of a protocol's predicate or establish acceptance.

### Initialization and publication

`new DIRECTORY` creates an absent directory. `init [DIRECTORY]` requires an
existing directory and defaults to the current directory. Both require the
companion compiler and create `zkc.toml`, `protocol.zkc`, `main.zkc` and input
templates for a minimal index echo. Existing manifests and conflicting source
files refuse without overwriting them. Existing regular input files are preserved.

`prepare [ENTRY]` uses the current manifest. With no selector it plans all declared
Entries; a library with none succeeds without publication. `Compiler::prepare`
returns checked interfaces and template contents before any files are published.
Planning uses the logical Interface and does not require executable lowering.
Existing regular input files are preserved byte for byte, regardless of contents;
symlinks, directories and other nonregular destinations refuse. Preparation
neither migrates obsolete maps nor removes inputs of deleted Entries. `check`
remains source-only; `inputs check` admits actual input values.

`inputs init` selects one Entry and creates only its nonempty input groups under
`inputs/<qualified.name>/` beside the manifest. Explicit-module and package modes
require `--output=DIRECTORY`. Static products retain their schema shape; unknown
leaves are null placeholders; prover keys show `file` and `fingerprint` placeholders.
Non-unit null inputs return `entry-input-unfilled`. Dynamic sizes and variant alternatives are never
guessed. Verification never selects witness files. Template publication never
replaces an existing file, including a file created after preflight. Multi-file
publication reports exactly which files succeeded if a later publication fails.
The `inputs init` report pairs generated `commands` with `requirements`;
`prepare`, `new` and `init` report requirements per Entry. `allow_header_only`
indicates explicit policy acknowledgement, and `setups` lists slots requiring
independent `--setups` authority and `--key` material. Neither is synthesized.

[File admission and publication](publication.md) defines regular-file checks,
protected output paths, result formats, staging and diagnostics. Opened input
and reference descriptors also protect their file identities from output aliasing.
Readable result values use the same native encodings as inputs where export is
permitted. Typed Rust ingress retains its independent immutable-value checks.

Generated Rust modules pin the exact package digest and delegate admission to the
common Host. They provide named participant/public input and output structures,
structural value conversions, and Rust representations of Boolean/index/unit,
array and nominal data. Mathematical leaves remain `entry::Value`, with concrete
domain and authority validation at invocation. Identifier conversion avoids Rust
keywords and collisions while retaining original source keys in conversions.
Serialized field and variant keys retain exact source spelling. Non-ASCII
identifiers, Rust keywords, `_` and names beginning `__zkc_` use that prefix
followed by lowercase hex of the full original UTF-8 bytes. Escaping the reserved
prefix makes this source-name encoding injective; it does not depend on rustc's
Unicode version. One allocator covers generated type, field, variant and helper
names in their namespaces and resolves preferred-name collisions. Generated naming-lint allowances cover these intentional spellings;
they do not disable general warnings. Fixed public-interface names are allocated
before source-derived names. Role conversion helpers and name constants delegate
to the same request/result maps. `ROLE`, `PROVER` and `VERIFIER` constants keep
source names, while native calls use roster-derived IDs.
Bindings emit no protocol algorithm or new execution/authority implementation.
Generated source is bounded by 16 MiB. Reauthorizing a different package requires
regenerating or deliberately replacing its pin.

The report's `native` member and the CLI's nested `execution` diagnostic retain
native participant and case labels. Source-name conversion applies to logical
request/result maps; it does not rewrite the native execution evidence format.
Entry command reports also expose `role_names`, mapping native participant labels
to source names. Human stop summaries use this map; native bundle commands retain
their own participant labels.

## Error phases

Calls that fail before execution return `EntryError`, whose `phase` identifies
package authentication, interface reading, setup authority, native admission,
interface binding, asset admission, request conversion or native preparation.
Phases identify where rejection occurred; `code()` identifies the reason. For
example, an unknown input name fails at `Request`, a missing packaged arena
fails at `Assets`, and an invalid native context or resource budget fails at
`Preparation`. Native preparation can also reject malformed input values.
Execution failures and cleanup remain in the report.
