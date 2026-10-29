# Structured native bridge

This optional bridge imports actual original protocol-profile MLIR with shared
helpers, finite folds, nested Local control and open protocol roots into the
common Lean region semantics. Each root retains its own participants and port
scopes. The checked profile includes Boolean, unsigned index, scalar/vector,
group and owner-local random-service values. See the
[native format](../../../docs/spec/formats/structured-source.md),
[formal contract](../../docs/spec/structured-source.md) and
[protocol targets](../../docs/design/structured-native-import.md).

`aggregates.py` separately checks actual native exports of ordered sequences
and nominal products with the independent Lean reader and evaluator. It covers
empty and duplicate inputs, component order, nominal identity and dormant
invalid types. It does not use the scalar-only C++ reference or claim native
execution correspondence. Run it with `--report PATH`, like the suites below.

`tables.py` retains the complete `CheckMembership` and `CheckRead` library
subjects, including their original realizations and formula contracts. It
checks the current native catalogue rows, finite computation admission,
selection masks, duplicate rows/queries, coordinates and callback read bounds.
Its participant replay uses the existing scalar test model only for equality
of canonical KoalaBear values; installed execution is checked separately by
`common/tests/protocol/test_table_relations.py`.

## Reproduce

`scoped.py` exports fresh source-language helpers through the scoped Func/CF
profile and checks them with the independent Lean reader and evaluator. Its
bounded cases cover branches, stopped arms, invariant loop captures,
mathematical requests, ordered finite callbacks and malformed formal binders.
It checks logical outcomes; it does not claim native execution or resource
equivalence. `lean-native` includes this suite in its bridge stage.

From the repository root in the pinned development environment:

```sh
cmake --build build/compiler --target zkc-compile zkc-structured_reference-test -j 4
(cd lean && lake build)
python3 lean/bridges/structured/check.py \
  --report build/experiments/structured-source/report.json
python3 lean/bridges/structured/open_protocol.py \
  --report build/experiments/structured-open/report.json
python3 lean/bridges/structured/scoped.py \
  --report build/experiments/structured-scoped/report.json
```

The suites' retained subjects (each one's Entry, sources and Lean data module)
are listed in [`fixtures.toml`](fixtures.toml); the cases run over each stay in
the suites' code. `--write-fixtures` replaces the retained exports and data
from the fresh ones. To refresh only this data boundary before checking its
downstream consumers, use the same selections without running security proofs:

```sh
python3 lean/bridges/structured/regenerate.py \
  --compiler build/compiler/zkc-compile --optimizer build/compiler/zkc-opt \
  --write-fixtures --output build/experiments/structured-regeneration
```

Omit `--write-fixtures` to compare exact bytes. `--fixture NAME` limits the
selection. This regenerates the manifest fixtures and the two finite-state
fixtures; subject manifests and the generic opaque fixture retain their own
generation paths. Admission and semantic checks remain separate.

The bounded generic opaque boundary has a separate source fixture and explicit
Lean registry. It needs only the compiler and local Lean modules:

```sh
python3 lean/bridges/structured/opaque_relations.py --compiler build/compiler/zkc-compile
(cd lean && lake build Tests.GenericOpaqueRelations && lake env lean --run bridges/structured/RunOpaqueRelations.lean)
```

`--write-fixtures` regenerates its retained MLIR, eleven-slot relation JSON and
constructor data through the compiler and `snapshot.py`. The Lean control reads
that JSON strictly, imports the full source unit and separately admits its
opaque rows against a registry fixed before evidence. Its kernel proofs identify
the selected predicate, including the static natural absent from the runtime
ABI, and show that another binding cannot replace it. It does not register GKR
or proximity families or supply their protocol theorems.

To add production execution comparisons, build `zkc` and supply it explicitly:

```sh
cargo build --release --locked -p zkc-cli --bin zkc
python3 lean/bridges/structured/check.py \
  --runtime target/release/zkc \
  --report build/experiments/structured-source-runner/report.json
```

The report records the source revision, deterministic seed, exact commands,
exported source and snapshot hashes, and retained executable hashes. Each run
allocates a fresh directory under `runs/` beside the selected report and links
its executables there before testing from a store holding one read-only copy
per content digest: `runs/tool-store`, or `ZKC_TOOL_STORE`, which `lean-native`
sets to one store in its run directory. Where links are unsupported it copies
them. The selected report is atomically marked `running` before setup, then
`pass`, `failed` or `interrupted`; it identifies the run directory and its own
retained report. Setup, source verification and finalization errors exit
nonzero; handled interruptions report `interrupted`.
Both report destinations are attempted even if one fails, and a publication
error triggers another attempt with failure recorded. A permanently unwritable
destination or an uncatchable process termination cannot be guaranteed a final
report. Ordinary runs never overwrite an earlier run's archive or tools.
`--compiler`, `--reference`, `--lean`, `--cases` and
`--seed` select explicit tools and generated cases. Failed comparisons retain
their source, requests and outputs beside the report.

Each run also retains `source-before.tar.gz` and a per-file byte manifest. For
the Git-backed drivers this snapshots **all tracked and nonignored untracked project files**, using
current working bytes, including modified authored fixtures, proofs, all local
imports, drivers, manifests and toolchain pins. Deleted tracked paths are
listed in the manifest. Archived contents are verified against the captured
bytes. This costs one compressed project tree per run; it avoids a manually
maintained partial source list. Ignored build outputs, `.git` history and
external dependency caches are excluded. Reproduction still needs the pinned
Lean toolchain and external packages from `lake-manifest.json`; this is not a
hermetic archive of the host or of the native compiler build environment.
The scoped repeat driver uses the Git-free inventory described below, with the
same archive and manifest schema. Before reporting success, the shared lifecycle
compares current source identities against that manifest, recording changed,
added, deleted, restored or unreadable sources as a failed `source-stability` check.
`--write-fixtures` instead retains a separate `source-after` archive because
source changes are intentional in that mode. Archive hashes describe the exact
bytes retained, not a simultaneous filesystem snapshot or a proof that copied
executables were built from those sources.
Extract the source archive into an empty directory to recover its working
tree. Initialize a Git repository and commit the restored tree there before
rerunning the Git-backed drivers (Git supplies their source inventory and revision); the retained report still
identifies the original revision and archived bytes. Build Lean with the pinned
dependencies and supply the archived native tools through the explicit flags.

## What is compared

The C++ test reference independently traverses original native SSA operands,
blocks and helper definitions. It does not read the exported JSON or call the
writer. Lean decodes the writer's arrays, independently checks their admission,
forms shared `Source.Region` bodies and runs owned operation meanings. A Python
integer reference checks arithmetic modulo the actual BLS12-381 scalar modulus.
Optional Runner cases additionally traverse preparation and realization with
ordinary native providers in both default finite selection and forced loop mode.

Cases cover ordered two-result accumulation; empty-result callbacks that abort;
empty, singleton and longer domains; predicate-before-step behavior; helper
reuse at distinct actual arguments; exact bound provenance through nested helper
calls and reordered/repeated helper results; identical finite invariant actuals;
nested conditionals; ordinary and conditional counted loops; capture
forwarding; original Protocol guards; and full-size scalar arithmetic. Actual
`.zkc` Entries exercise both element and indexed accumulation through frontend
elaboration. Well-formed result permutations
and changed stop reasons are accepted as different programs. Malformed dormant
bodies, cycles, unsupported vocabulary, extra fields, invalid references and
wrong same-typed containers/captures are refused.
Every other installed field, group and random service exports its native
catalogue rows; Lean decodes them, finds them consistent and refuses them only
because its environment does not list them (or, for BLS12-381 G2 and GT, does
not admit that sort instance).
Boundary cases also compare exactly 4096 instructions and a complete 1 MiB
export, including its final newline. The reference counts stored instructions
in the same units as the format; its dynamic execution budget is separate.
Used Unicode and newline-containing helper names traverse native export,
independent import and evaluation without renaming.

Runner comparison observes ordered outputs, completed versus stopped execution,
the stop class, and empty active-frame/live-resource counts for these bounded
runs. It does not equate the full native event, diagnostic or resource model to
the Lean process. A nonzero Runner exit can report an expected semantic stop;
the bridge checks the structured result before classifying it.

## Lean reference executable

The `structured-source` executable in `ZkcTools.StructuredSource` checks and
runs admitted snapshots, and prints participant normal forms:

```text
structured-source check SNAPSHOT.json
structured-source run SNAPSHOT.json INPUTS.json
structured-source open SNAPSHOT.json REQUEST.json
structured-source normal-form SNAPSHOT.json REQUEST.json
```

A `normal-form` request is an array `[protocol, repeat, role, roster, pattern,
laws, strict]`: the protocol's retained name, the site of the repeat whose
callback is normalized (or `null` for the body), the role and roster size as
decimal strings, one input pattern entry per input (`"absent"`, `"present"`,
`"optional"`, or a fixed `["index", "0"]`, `["field", "1"]` or `["bool", true]`),
the laws (`[helper, "returns" | ["stops", reason], pins]`, a pin being `null` or
an input position) and whether owned calls without a law are kept. It prints
the compiled normalizer's form as JSON for inspection, with `names` set
when laws had to be chosen by helper name as well as by signature; the run is
not trusted, since the kernel checks every printed form.

Closed runs take and return typed input/output arrays. Open requests and
results follow the native schema: optional ordered inputs, selected role,
scripted replies, full request/reply/stop records, stop site and consumed reply
index. Missing replies stop `incomplete`; mismatches stop `refused` without
consuming the mismatching reply; valid scripted stops consume their reply.
Unused script suffixes remain unconsumed.
Aggregate inputs retain every ordered product component and sequence element.
The execution tool's preliminary capacity analysis joins corresponding product
components and equal-length sequence elements when a branch is unknown. An
unknown branch producing different sequence lengths yields an unknown bound
and may cause tool refusal. This conservative execution-tool policy does not
change the source model's branch or finite-fold semantics. Nested aggregate
storage and output serialization contribute to the tool's capacity accounting.
An oversized received vector is an observer capacity error; a malformed reply
shape or element type remains an unconsumed semantic refusal. Requests are
limited to 1 MiB; snapshot admission limits belong to the
[formal contract](../../docs/spec/structured-source.md#checked-subject).

The CLI chooses `F = G = ZMod scalarModulus`, an explicit additive test group.
This is not native BLS G1 semantics. Typed arbitrary-group equations protect
distinctions that commutative scalar test arithmetic cannot detect.

### Bounds preflight

Executable work bounds are separate from fuel-free denotation. The Lean observer
and native SSA evaluator count different work, so their exact exhaustion
thresholds are not equated. Comparisons of outcomes, traces, sites and consumed
replies use sufficient capacities; capacity refusals are tested separately.

Before interpretation, `ZkcTools.StructuredSource.Bounds` propagates per-value
index intervals, vector-length intervals and optional presence through the
checked source. This includes generated constants, arithmetic, append, helper
bodies, loops and folds; an input maximum alone is insufficient. Typed received
values use conservative bounds from all matching reply envelopes, including
unused suffixes. A reversed array stores the abstract SSA context while ordered
argument/result tuples retain their list ABI. Protocol transfers capture their
strict prefix, compare complete signatures, compose the same root-coordinate
context and preserve actual optional inputs and mapped masks. An outside call
returns the abstract absent tuple; no returning path is distinct from a returning
empty tuple. Typed receives use independent reply envelopes, never the sender's
operand. The preflight never infers a helper's behavior from its spelling and
does not replace the typed evaluator.

The map transfer intersects all retained row-length intervals and charges every
length extraction before helper work. On a possible nonempty return, it analyzes
the actual helper once on the complete scalar atom tuple and reserves that
helper's logical work for each possible row, including dead nested calls. The
resulting vector is bounded by the common successful length; aggregate tuple
work does not consume a different per-vector capacity. Empty rows avoid helper
work only after all shapes pass. Maps add no separate analysis, execution or
vector limit. The workload meter counts logical tuple selections; it does not
count the depth of concrete positional list indexing as processor steps.

Repeat preflight reuses conservative `Bounds.iterate`. An outside participant
returns abstract absent state without analyzing callback execution. An absent
active count or an interval whose lower bound exceeds maximum has no returning
path. Otherwise `min(upper, maximum)` bounds abstract exploration only; concrete
counts above maximum still stop `refused`. The analysis masks initial and
yielded state and preserves optional captures and the captured protocol table.
It joins the initial state and analyzed prefixes, even when a callback has no
returning path, and may analyze later abstract steps. These joins can include
states unreachable at a known positive count. No-return (`none`) remains
distinct from a successful empty state (`some []`). Planned traversal work is
charged before callback analysis, under the same work, vector and reply limits.

Separate analysis and expanded logical-work meters each allow 1000000 units;
generated vectors are capped at 4096 elements. Work includes nodes, selected
operands, tuples, allocated ranges and vector traversal/serialization. It is
not an exact host instruction, allocation or wall-time bound. Analysis charges
its own expansion and context operations. A known branch or select condition
chooses its reachable alternative after strict/optional presence handling;
unknown conditions join both alternatives. Loop joins and typed unused replies
can still overapproximate the executed path, so a cheap logical run may fail
preflight; a valid source equation does not imply preflight success. Such
diagnostics are tool-capacity refusals, distinct from the process's semantic
stops. Analysis exhaustion reports `structured-bounds-analysis-limit`;
unsupported or mismatched abstract shapes report `structured-bounds-unknown`.
Work and generated value caps retain separate closed/open diagnostics. Helpers
are resolved in a bounded per-preflight table with full signature validation,
preserving their checked bodies and ordinary linking.

These transfers are conservative executable controls. Their soundness,
agreement with native capacity thresholds and processor costs are not proved,
and finite controls do not show that every input satisfying a source theorem is
admitted by this observer.

## Actual proof subjects

The native [`total-state.mlir`](../../../compiler/test/fixtures/finite/total-state.mlir)
and [`unit-state.mlir`](../../../compiler/test/fixtures/finite/unit-state.mlir)
are the canonical subjects. Their retained JSON is `protocol-structured` output.
The bridge compares the source-byte digest, the entire exported snapshot and regenerated
transparent constructor data used by
[`TotalState`](../../ZkcExamples/Structured/TotalState.lean) and
[`UnitState`](../../ZkcExamples/Structured/UnitState.lean).

```sh
python3 lean/bridges/structured/snapshot.py \
  lean/bridges/structured/fixtures/total-state.json \
  lean/ZkcExamples/Structured/TotalStateData.lean \
  --namespace ZkcExamples.Structured.TotalStateData
```

The renderer emits data only. Admission and semantic equations are separate
kernel-checked declarations. Changing a fixture requires reviewing those
equations, rather than merely updating an identity string.
UTF-8 names remain data inside escaped Lean string literals. The independent
renderer check compiles generated declarations and compares their exact Unicode
codepoints in the kernel, including controls, quotes, backslashes, multibyte
length boundaries and text resembling Lean declarations. Its CLI control also
runs under an ASCII locale; source files and tool output use explicit UTF-8:

```sh
python3 lean/checks/check_structured_renderer.py
```

This check runs in `just test-lean`. It does not turn the renderer into a proved
translator.

[Formal support](../../docs/support.md#finite-fold-subjects) states the proved
process equations for both subjects.

### Typed bodies and generated views

A proof subject is admitted from literal typed bodies: `structured_views`
(or `structured_closed_views` for a single-role closed root) emits the checked
payload and one kernel equation per admission phase from them. `bodies.py`
prints those bodies for a retained snapshot:

```sh
python3 lean/bridges/structured/bodies.py \
  --data ZkcExamples.Structured.SchnorrHelpersData \
  --namespace ZkcExamples.Structured.SchnorrHelpersBodies \
  --name s13h7363686e6f72725f666f726d738h726573706f6e7365=response \
  --output build/experiments/bodies/SchnorrHelpersBodies.lean
```

It admits the snapshot with the checker in a scratch module, materializes each
checked helper, protocol and (with `--closed`) projected root body, and prints
them as `<|` chains. `--name DECLARATION=local` replaces the default
`helperN`/`protocolN` name of that retained declaration; `--check` compares the
printed module with the existing file instead of writing it.
The printed module is ordinary source, not an admission certificate: a wrong
or stale body fails the generated phase equations. The subject driver
(`lean/bridges/subject.py`) prints the Bodies and generates the Views of every
subject manifest that owns them, and compares them under `--check`; the Entry's
protocol takes the manifest's local name and a unique relation formula is named
`formula`.

### Generated participant normal forms

The shared Lean `Bindings.RoleViews` printer derives role-local process views
from the admitted source and its typed normal forms. The source determines
input visibility, complete return masks, callee arguments, callback state and
loop captures. Catalogues in `Tests.Generators.ScalarViews` and
`Tests.Generators.GkrPresentations` choose source snapshots and display names.
They cannot override the source's operation order or route semantic slots.

```sh
python3 lean/bridges/structured/source_views.py --check
python3 lean/checks/check_source_views.py
```

The first command regenerates all maintained selections and compares exact
bytes. Omit `--check` to write the outputs, or pass selection names to limit
the work. The second also checks every emitted Lean module and the semantic
controls. Python schedules these commands and compares physical outputs; it
does not interpret participant instructions or propose their proofs.

| Selection | Subject |
|---|---|
| `ChaumPedersen`, `SchnorrAnd`, `SchnorrInteractive`, `Okamoto` | Both roles of the retained Sigma source and its complete root outputs |
| `SumcheckSource`, `SumcheckReduction`, `SumcheckRepacked` | Both roles, the reduction callback, source-specific input and return layouts, and complete mathematical helper/body associations |
| `Gkr` | Both roles of the original GKR Entry, its layer Sumcheck applications and nested output-point, layer and coefficient callbacks |

Every emitted process equation is kernel checked against the admitted typed
body. The normalizer's soundness theorem connects the form to that body;
occurrence-preserving equations retain call and loop coordinates. Invocation
mask and loop-presentation laws handle missing inputs, stopped paths and full
returns. A stale body or wrong same-sort operand is a failed equation.

Mathematical refinements remain authored library consumers. Sigma modules
retain their transcript, formula, contract and acceptance facts. Sumcheck's
shared mathematical forms are computed by the existing Lean normalizer, and
full typed-body associations establish that a source may use its helper and
callback laws. GKR's helper mathematics, state invariants and root property
assembly also remain authored. Generated structural views do not establish
these mathematical facts or native execution correspondence.

Subject manifests select these outputs with `[source_views] selections`.
The subject driver rebuilds every selected output before recording success;
the report freshness join hashes the same complete output inventory. The old
Python normal-form evaluator and its TOML request language are removed.

### Adding a structured subject

A subject is a manifest in [`lean/subjects`](../../subjects/README.md); the
subject driver does every mechanical step from it. From the repository root in
the pinned development environment, with the compiler built (`just build`) and
Lean set up ([development guide](../../../docs/development/README.md)):

1. Write the protocol in a project module. Select a closed protocol application,
   for example `sigma::ChaumPedersen<example::G>`; no host Entry wrapper is needed.
2. Write the manifest: its sources (a project or a module map), that closed
   application under `[entries] interactive`, the structured profile, and under `[generated]` the
   retained export (`interactive_export`, `interactive_source`), the data module
   (`interactive_data`) and, to admit the unit from printed bodies, the Bodies
   and Views modules (`interactive_bodies`, `interactive_views`), as
   [`chaum-pedersen.toml`](../../subjects/chaum-pedersen.toml) does.
3. Run `python3 lean/bridges/subject.py --subject NAME --write`. It exports the
   selected subject, renders the data, builds it, prints the bodies and writes the Views
   module, which admits the unit with `structured_views`; `--check` later
   requires all of them to be unchanged.
4. Add a Lean source-view catalogue selection and name it under
   `[source_views] selections`; the driver regenerates and checks every output.
5. State the protocol's mathematics over the generated declarations and connect
   it to a library, as
   [`ChaumPedersenBinding`](../../ZkcExamples/Structured/ChaumPedersenBinding.lean)
   (extraction from two accepting transcripts) and
   [`ChaumPedersenSigma`](../../security/ZkcSecurity/Examples/ChaumPedersenSigma.lean)
   (VCVio's Schnorr Σ-protocol at the base pair) do. The package treats warnings
   as errors: a lemma that does not use every section instance needs
   `omit [...] in`, written before its docstring.
6. List the new modules with `python3 lean/checks/audit_imports.py --write`, build
   (`python3 scripts/develop.py lean --deps main`, and `--deps arklib` for a
   library connection) and run `python3 common/tests/run.py lean`.

A compiled proof Entry is added the same way with `[entries] proof` and the
construction profile; the driver then also generates its constructed
participant data, printed bodies and per-Entry glue
([construction bridge](../construction/README.md)).

### Constructed pair completeness roots

[`generate_component_roots.py`](generate_component_roots.py) assembles source,
actual constructed pair, typed input ABI, whole-process views, fixed Subject,
canonical completeness theorem and claim receipt. Its configuration lives in
[`roots/sampled.toml`](roots/sampled.toml), separately from the subject manifests.
The installed Sigma method proves the actual Schnorr and Schnorr AND producers
with private draws and a shared public challenge. An additional root borrows one
random service under two aliases before invoking Schnorr AND. A direct theorem
selection installs the sampled-abort control and its nonzero bound through the
same Subject, ABI, canonical endpoint and receipt printers. `SequentialSigma` composes Schnorr and
Chaum–Pedersen through the same method, drawing its second private nonce after
the first protocol's challenge and response.

With the security dependencies built, run from the repository root:

```sh
python3 lean/bridges/structured/generate_component_roots.py \
  --compiler build/compiler/zkc-compile
```

The driver checks ordinary generated Lean files in an isolated
`build/lean/component-roots/lib` tree without running a Lake build. `--check`
requires exact regeneration, `--only NAME` selects roots, and `--phase` selects
export, assembly, proof or receipt. `--dependency-path PATH` supplies another
prechecked dependency tree when collaborators use separate output directories;
serialize writers to a single output tree. Objects owned by those explicit trees
take precedence over their inherited cache symlinks, in argument order. Existing
objects owned by the output tree remain its responsibility; recheck an affected
module when its source or import closure changes.

The `zkc.component-roots/0` descriptor requires nonempty strings `schema`,
`model_module`, `model`, `sampling`, `field_type`, `group_type`, and
`capabilities`, plus a nonempty `root` array. Optional top-level
`receipt_normalization` and `theorem_normalization` values are lists of nonempty
strings naming Lean declarations. Every root requires nonempty strings `name`,
`source`, `entry`, `target`, and `method`, and a `modules` map from nonempty
module names to nonempty source paths. Root names must be unique identifiers.

The installed `sigma` method selects zero error and generates
its own proof module and theorem. Optional `method_imports` names additional Lean
modules, and `nonvacuity_law` supplies a term checked as `Nonvacuous subject` for
the fixed generated subject. Without that term, the method proposes the default
zero witness and must prove its admission. These hooks install mathematical
evidence; they cannot replace the subject's relation, retained input clauses or
input policy. `method_imports` is a list of nonempty strings and
`nonvacuity_law` is a nonempty string. Both are refused for the `direct` method.
The `direct` method additionally requires
`proof_module`, `error_bound` (a Lean `ENNReal` term) and `error_expression`
(request expression syntax). It permits `proof_name`, defaulting to
`<proof_module>.compiled_ideal_complete`. Its generated endpoint checks the
selected theorem at `error_bound`; the canonical receipt independently checks
agreement with `error_expression`. Both fields are required even for a direct
zero-error theorem. The Sigma method refuses these fields because its installed
adapter proves perfect completeness. These values must be nonempty strings.
Unknown keys, missing required keys, wrong value shapes, duplicate
names, unsupported methods and invalid selections fail before constructing the
generator, invoking native/Lean tools or creating output directories. Validation
includes unselected roots. A misspelled bound never activates the zero default.
Run the focused production-entry refusal checks with
`python3 lean/bridges/structured/component_roots_tests.py`.

The security test scope also runs `security/checks/check_abi_installations.py`.
It compiles freshly emitted ABIs and completeness proofs for ordered, permuted,
repeated and heterogeneous selectors, empty public data, and constrained input
policies. It refuses incorrect selector equations, clause interpretations and
nonvacuity terms. Fully empty source rows are checked as emitted structural
declarations; admission of a service-free pair is not added by those controls.

`ZkcTools.StructuredSource.Root` owns common Subject and receipt assembly.
`Generation.RootCompleteness.Selection` associates an existing indexed Subject,
canonical endpoint and explicit error with its request output. The indexed
Subject and ABI already own the typed source/artifact association.
`RootCompleteness` owns the endpoint declaration used by maintained table roots,
Sigma readback and direct quantitative proofs. Table mathematics and Sigma
readback remain installed methods. Family extensions supply their
mathematics and proof method; `Generation.UniformRoot` is an optional model
presentation helper. Root configuration selects sources, nominal model,
installed method or direct theorem and numeric error expression. It supplies no
occurrence paths or structural proofs. Every emitted proof and receipt must
elaborate independently.

`OriginalRoot.templateSource` and `TemplateInstallation.source` assemble generic
original-body templates and typed library-law installations. Their inputs retain
the exact nominal model, helper table, role, callee signatures and immutable
earlier protocol prefix. The public-table Sumcheck printer is an ordinary method
in `ZkcTools.StructuredSource.Methods.SumcheckRoot`; its field, ABI and mathematical
restrictions do not constrain the shared template printer. Its actual linear
Reduce input carries both the pending point and value. Library correspondence
allows an existing prefix and a restricted producer table while keeping the
original reference table fixed. The current root clients initialize an empty
prefix explicitly.

`bridges/structured/check_root_composition.py --compiler COMPILER` checks a fresh
four-call source with the production printers in a private overlay, including
the canonical honest completeness, scalar soundness and charged soundness
receipts. `--resume --phase receipts` reuses that overlay's checked body proofs
and reissues the actual source requests. The acceptance check requires the named
receipts to exist; successful printing alone is insufficient. One- and two-call
clients retain their generated roots and exact source requests in the normal
source tree. These checks concern the compiled ideal experiments and establish
no native execution or performance correspondence.

`security/checks/check_root_assembly.py --output DIRECTORY` compiles fresh
readback, direct quantitative and canonical receipt outputs in a private overlay.
It accepts `--dependency-path PATH` for prechecked dependencies and never runs a
Lake build. Controls reject a wrong Subject, wrong theorem bound and mismatched
request quantity. These model fixtures do not replace regeneration and receipt
checks on the actual exported roots.

`lean/checks/check_subject_roots.py --exports DIRECTORY` checks the maintained
table roots against retained native exports, exact generated outputs and kernel
preservation equations. Each catalogue-named directory contains `source.json`,
`producer.json`, `validator.json`, both participant `.identity` files,
`original.mlir`, `interface.json`, `source-claims.json` and `deployment.json`.
The same check regenerates the compiled-stage source request declarations through
the common data renderer; Lean resolves their properties, models and evidence.
Reissuing a request requires `validator.identity` to contain the current
`validator.json` bytes. Changed identities require an explicit request migration;
the checker does not reinterpret a historical receipt as evidence for new bytes.
Use `--write` to retain regenerated output and `--dependency-path PATH` for a
prechecked private dependency tree. A successful generation comparison does not
replace checking the corresponding canonical receipt clients.

These roots use `blsScalarModel`: the source's nominal BLS scalar/group tags are
retained, while the groups are interpreted as additive modules over the scalar
field. Completeness concerns the actual ideal pair under the canonical honest
sampling experiment. It establishes neither native curve realization nor a new
discrete-log security result. Local draws use installed producer capabilities;
they are absent from user data inputs and from the public random-oracle cache.

## Open participants

The open suite compares the original native SSA interpreter with the independently
admitted Lean participant process. Requests retain the selected role, original
input positions, service handles, exact action sites and a sequence of typed
replies. Receives use the supplied reply; a common source input does not identify
values independently supplied to different participants.

The group model in this suite is explicitly the additive scalar group, with
scalar multiplication interpreted as field multiplication. It tests source
wiring and ordered interactions; it does not execute BLS12-381 points. The Lean
process equations separately quantify over a lawful scalar/group module.

Cases include independently available helper results, unused intermediate
requirements, zero-result Local calls, distinct and aliased service handles,
guards, every supported stop class, wrong/missing replies, group operations,
alternate participant rosters and malformed whole-unit metadata. Actual Schnorr
Entries exercise both roles, altered replies, helper factoring, declaration
permutation and an early-challenge mutation. The latter can accept the same
sample while exposing a different first action. The Schnorr AND and
Chaum–Pedersen Entries of the [Sigma project](../../../examples/projects/sigma/README.md)
retain their MLIR, JSON and constructor data; their cases exercise both roles,
an altered response in each AND component, an abort at each verifier action and
a Chaum–Pedersen statement whose keys use different witnesses.

[Formal support](../../docs/support.md#interactive-schnorr) states the proved
equations for these Schnorr subjects.

`open_protocol.py --write-fixtures` regenerates each retained MLIR, JSON and
constructor-data subject. As for the closed suite, semantic proofs are maintained
separately. Missing replay input is
reported as `incomplete`, an observation of an unfinished interaction rather than
a claim that a production endpoint has terminated.

## Scalar inlining pairs

Two tiny authored single-role Entries retain mathematical helpers in their
original native MLIR:

| Subject | Scalar contract | Helper structure |
|---|---|---|
| [`schnorr-response.zkc`](fixtures/schnorr-response.zkc) | `nonce + challenge * secret` | One response helper |
| [`sumcheck-claim.zkc`](fixtures/sumcheck-claim.zkc) | `(1-r) * a0 + r * a1` | One claim helper calling the same weighted-product helper twice |

The Sumcheck source uses `weighted(a0, 1 - r) + weighted(a1, r)`; the decimal
literal is admitted by kernel reduction. Both computations are scalar
ingredients of protocols, without group operations or interactive security
claims.

[`SchnorrResponse`](../../ZkcExamples/Structured/SchnorrResponse.lean) and
[`SumcheckClaim`](../../ZkcExamples/Structured/SumcheckClaim.lean) are the proof
clients for these pairs. The retained mutation changes only the prepared
response entry's addition to subtraction. It passes native formation and Lean
admission. [Formal support](../../docs/support.md#helper-inlining-pairs) states
the proved original/candidate equations and the mutation's counterexample.

After building Lean and the existing native tools, reproduce from the root:

```sh
python3 lean/bridges/structured/inlining.py \
  --compiler build/compiler/zkc-compile \
  --optimizer build/compiler/zkc-opt \
  --reference build/compiler/test/zkc-structured_reference-test \
  --report build/experiments/structured-inlining/report.json
```

This focused sibling reuses the bridge driver. It compiles the Entry package, selects its single native Run deployment, then runs the actual
`--zkc-prepare-protocol="simplify=false optimize-finite=false"` command. It
exports both sides with `protocol-structured`, independently admits them,
compares exact retained MLIR/JSON/constructor bytes, and rechecks the proof
sources. Candidate snapshots use the format's `original` tag because each
export describes its supplied native input; their input is the retained
prepared MLIR. The entry contains no helper calls, although dormant helper
declarations remain in the module.

Default finite comparisons use four boundary/example tuples and sixteen seeded
full-size scalar tuples per subject, through both direct native SSA and Lean
execution. The admitted mutation is also compared. Reports retain commands,
outputs, complete project-source bytes and tool copies with hashes, toolchain,
affinity and thread settings. The
existing `just test-lean-native` scope includes this sibling. Host-level lock
coordination belongs to the invoking validation session.

`--write-fixtures` intentionally replaces the retained native subjects, exports
and constructor data. It never generates or changes semantic proofs; review
the changed subject and its checked body equations. These files follow the
`TotalStateData` pattern as actual proof subjects. Research logs and executable
copies remain in the run directory under `build/experiments`. Regeneration also
retains `source-after.tar.gz` so the archive contains the resulting fixture
bytes as well as the original working sources.

These model equations and finite native comparisons are separate evidence.
The writer, parser and renderer are tested executable boundaries. This package
does not prove C++ export correctness, frontend translation, native lowering,
production arithmetic/sampling or runtime capacity equivalence. The source-level
Schnorr theorem has its own algebraic and interaction assumptions.

## Primitive bindings and unchanged library helpers

`primitives.py` emits five complete original-stage units from the maintained
`compiler/test/fixtures/structured-source/primitive-callers.zkc` caller and unchanged
standard libraries. The first three call `multilinear::has_shape`, `table` and
`halves`; an independent sequence example uses append, length, sum, equality and
checked integer arithmetic. A two-role index example checks pure expressions
and absence at the nonowner.

```sh
python3 lean/bridges/structured/primitives.py \
  --compiler build/compiler/zkc-compile \
  --reference build/compiler/test/zkc-structured_reference-test \
  --report build/experiments/structured-primitives/report.json
```

The native reference walks original SSA; Lean separately admits the current
snapshot, including every binding declaration. Python expectations use ordered
lists, integer arithmetic and the equation `length = 2^dimensions * columns`.
Tests distinguish false shape results, rejected table construction and checked
arithmetic refusal. Non-symmetric tables expose swapped halves. Invalid unused
bindings, incompatible nominal arguments, duplicate names, implementation
selection and binding-as-callable mutations exercise the independent reader.

The suite compares retained original MLIR, exported JSON and transparent Lean
constructor data byte-for-byte. `--write-fixtures` updates those subjects and
requires review of their semantic proofs; it does not produce a proof. The
ordinary `lean-native` check includes this suite. Passing these finite
comparisons does not establish universal exporter, native arithmetic or resource
correctness.

## Retained maps and realizations

`maps.py` uses five complete original units from
`compiler/test/fixtures/structured-source/map-callers.zkc` and the unchanged
standard libraries. The library clients fix the first coordinate of a multilinear
table, fix an ordered prefix, and extract a validated table's values. Two
independent clients map an interleaved scalar/vector formula and a constant
formula with unused row inputs.

```sh
python3 lean/bridges/structured/maps.py \
  --compiler build/compiler/zkc-compile \
  --reference build/compiler/test/zkc-structured_reference-test \
  --report build/experiments/structured-maps/report.json
```

Realization retains the exact Math helper and full signature. A map retains its
scalar helper and row mask; all row lengths are checked before the helper is
invoked in order. An unused row still constrains shape, and an owned Local call
requires every argument. Independent expectations use contiguous low/high
halves, `low + (high - low) * coordinate`, and ordered prefix restriction.
Asymmetric tables, interleaved arguments, zero dimensions, excessive prefixes,
shape failures, and missing owner inputs distinguish these rules.

The independent Lean-reader controls mutate retained records directly, including
Boolean masks, exact record arity, helper signatures and visibility, dormant
declarations, and a dead transitive call outside the scalar ring fragment.
Native MLIR formation already rejects many corresponding malformed modules;
those native failures alone do not test the independent reader's closure check.
The bridge retains exact source, MLIR, JSON and constructor data using the same
receipt format as the primitive suite. It is included in `lean-native`.

These comparisons concern original declarations and their shared structured
semantics. They do not establish the correctness of native map lowering or
transport a cryptographic security theorem to production execution.

## Retained protocol applications

`applications.py` retains complete original units for the existing
`application.zkc` and `service_order.zkc` fixtures, plus a nested service caller.
The first composes arithmetic protocols with a role permutation. The second
makes the order of service draws and message delivery observable across a call.
The nested caller exercises accumulated site qualification.

```sh
python3 lean/bridges/structured/applications.py \
  --compiler build/compiler/zkc-compile \
  --reference build/compiler/test/zkc-structured_reference-test \
  --lean lean/.lake/build/bin/structured-source \
  --report build/experiments/structured-applications/report.json
```

The C++ reference traverses original native SSA with an explicit participant
mapping and call prefix. Lean independently checks full signatures and builds
closures over earlier protocol declarations. Calls preserve optional inputs;
only owned Local helpers impose strict input presence. A participant outside a
callee's mapped roster skips that call, including a zero-result child that
would stop for an inside participant. Nested action sites follow the native
naming rule; helper-internal sites keep their own namespace. Native one-role
closed execution also supports calls, which the Lean closed projection refuses;
paired application comparisons therefore use open execution and record the
closed-view refusal separately.

Independent expectations check arithmetic results, received values, aliased and
distinct service handles, every reached service/message stop, missing replies,
and mismatched reply sites. A stateful script supplies the expected handle order;
its counter values do not come from either tested interpreter. Complete-source
renaming preserves behavior, while a well-formed arithmetic mutation changes it.
Malformed snapshot controls exercise the separate reader and are not claimed to
identify mutated native source bytes. `--write-fixtures` regenerates exact MLIR,
JSON and transparent Lean data, while semantic proofs remain separately maintained.

This suite compares the original-SSA reference and the Lean observer. The
production Runner has a separate comparison suite below. These application
comparisons do not prove native projection, arbitrary provider behavior, or a
security reduction. Retained scoped repeats are covered by the suite below.

## Retained scoped repeats

`repeats.py` re-emits the complete original `repeat.zkc`, `repeat_nested.zkc`,
service Demo/Nested, Reduction and Sumcheck entries. Project manifests select
both Sumcheck module closures. Original MLIR, snapshot JSON and the six
maintained Lean Data files must match byte-for-byte; this driver never rewrites
fixtures. Frontend participant names and positional interfaces are preserved.

```sh
python3 lean/bridges/structured/repeats.py \
  --compiler build/compiler/zkc-compile \
  --reference build/compiler/test/zkc-structured_reference-test \
  --lean lean/.lake/build/bin/structured-source \
  --report build/experiments/structured-repeats/report.json
```

`OpenSuite` compares actual original SSA with the independently admitted Lean
observer and explicit Python expectations. Cases separate participant inputs,
counts, received values and service draws; exercise captured values, carried
state masks, nested callbacks, ordered service aliases, static action names,
missing input, bounds, guards, stopped prefixes and unused replies. Complete
same-name source and arithmetic changes must change observed behavior.
Independent MSB-first table arithmetic supplies the zero-, one- and two-round
Reduction/Sumcheck expectations, including false claims and guard rejection.

Malformed wire controls test the independent reader. Their copied digest does
not assert identity with mutated native source bytes. Native affine values
outside Lean `Ty` are explicitly skipped. Native closed repeat execution and
its intentional formal closed-profile refusal are recorded separately.
Renderer checks construct data and inspect it with the kernel; they do not
produce semantic proofs or duplicate whole Sumcheck admission checks.

The suite is registered in `lean-native`. Its Git-free receipts use the shared
archive, tool capture and report lifecycle. The inventory follows the main
Lake package's declared library namespaces and executable roots, including
`ZkcTools` and its local observer dependencies. It also captures the structured
bridge and fixtures, Python sources in `scripts/`, `common/tests/support/`,
`lean/checks/` and `lean/support/`, the common test entry point, compiler source
owners (`include/`, `lib/`, `tools/`, `test/`, `cmake/`) and their shared
`common/unicode/` inputs, package manifests and
pins, and the authored module/manifests selected through each subject's project
closure. New modules within those owners enter the inventory automatically;
adding a dependency in a different owner requires extending this scope.

This is a source archive for the main formal package and repeat driver, not a
whole-checkout archive. Hidden directories, private experiments, build caches,
external packages and optional Lean integrations are excluded. Directory links
within scanned owners are refused rather than traversed. The selected native
executables are copied and hashed; reproducing their build environment remains
separate. Restoring the archive does not require initializing Git to rerun
`repeats.py`; the report's revision is null and the manifest identifies its
working sources. Deleted or unreadable required inputs fail setup, and changes
or read failures after capture fail finalization while retaining the original
archive and prior runs.

`--native-only` supports development while the formal CLI is unavailable and
reports `native-only` with exit zero only when its checks and evidence lifecycle
succeed. Setup, comparison or finalization failures still report `failed` (or
`interrupted`) and exit nonzero; they cannot become a native-only success.
These finite comparisons establish neither universal exporter/native
correspondence nor symbolic Sumcheck or security theorems.

## Native participant observations

The optional [participant comparison](participant.md) binds actual Interactive
Schnorr source and checked projection to Rust endpoint execution, canonical
BLS12-381 G1 bytes, pending prefixes and provider residual observations. Its
sampled generator-multiple relation and narrow stop adapters are separate from
the source semantics and do not establish native refinement.
