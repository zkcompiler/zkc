# Structured native bridge

This optional bridge imports actual original protocol-profile MLIR with shared
helpers, finite folds, nested Local control and open protocol roots into the
common Lean region semantics. Each root retains its own participants and port
scopes. The checked profile includes Boolean, unsigned index, scalar/vector,
group and owner-local random-service values. See the
[native format](../../../docs/spec/formats/structured-source.md),
[formal contract](../../docs/spec/structured-source.md) and
[protocol targets](../../docs/design/structured-native-import.md).

## Reproduce

From the repository root in the pinned development environment:

```sh
cmake --build build/compiler --target zkc-compile zkc-structured_reference-test -j 4
(cd lean && lake build)
python3 lean/bridges/structured/check.py \
  --report build/experiments/structured-source/report.json
python3 lean/bridges/structured/open_protocol.py \
  --report build/experiments/structured-open/report.json
```

To add production execution comparisons, build `zkc` and supply it explicitly:

```sh
cargo build --release --locked -p zkc-tools --bin zkc
python3 lean/bridges/structured/check.py \
  --runtime target/release/zkc \
  --report build/experiments/structured-source-runner/report.json
```

The report records the source revision, deterministic seed, exact commands,
exported source and snapshot hashes, and retained executable hashes. Each run
allocates a fresh directory under `runs/` beside the selected report and copies
its executables there before testing. The selected report is atomically marked
`running` before setup, then `pass`, `failed` or `interrupted`; it identifies the
run directory and its own retained report. Setup, source verification and
finalization errors exit nonzero; handled interruptions report `interrupted`.
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

`TotalState.process_eq_checked_reference` proves the ordered pair fold for
arbitrary lists, including refusal outside the unsigned-index domain.
`UnitState.process_eq_checked_reference` proves the complete result: an admitted
nonempty list aborts exactly when its predicate enables the zero-result step.
Both are parametric in the scalar commutative ring. They are equations for the
actual admitted constructor subjects; no finite test enumeration supplies them.

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
sample while exposing a different first action.

`SchnorrInteractive` proves equations for both participants of the retained
library-derived source, and connects the verifier through an explicit effect
adapter to its reusable Schnorr contract. The dormant relation declaration and
Math formula are both retained with an explicit checked formula symbol. The
contract table retains every protocol's clauses, including empty inventories.
`SchnorrBinding` uses this metadata to select the actual target's ports, roles,
decision and formula body. These source equations keep received values and stopping continuations.
They do not establish that the native runtime or provider implements them.

`open_protocol.py --write-fixtures` regenerates each retained MLIR, JSON and
constructor-data subject. As for the closed suite, semantic proofs are maintained
separately. The native reference and Lean observer have separate work budgets;
normal results are compared with sufficient capacity. Missing replay input is
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
[`SumcheckClaim`](../../ZkcExamples/Structured/SumcheckClaim.lean) prove complete
process equality between each exact imported original and the actual prepared
candidate, for every input in any `CommRing F` with `DecidableEq F`. Each client
uses named checked-body contracts. The response proof applies
`Structured.inline_invoke`, whose lookup/body premise covers every actual tuple;
it preserves stops and the caller's suffix without a totality assumption.
The controls in `Tests.StructuredInlining` cover stopping and returning
zero-result helpers, suffix stops, retained caller values, repeated arguments
and ordered multiple results.

The retained mutation changes only the prepared response entry's addition to
subtraction. It passes native formation and Lean admission. The kernel proves
that `(nonce, challenge, secret) = (2, 3, 5)` returns `17` in the original model
and `-13` in the mutated integer model.

After building Lean and the existing native tools, reproduce from the root:

```sh
python3 lean/bridges/structured/inlining.py \
  --compiler build/compiler/zkc-compile \
  --optimizer build/compiler/zkc-opt \
  --reference build/compiler/test/zkc-structured_reference-test \
  --report build/experiments/structured-inlining/report.json
```

This focused sibling reuses the bridge driver. It runs `language-emit` and
`language-interface`, then the actual
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
Schnorr theorem has its own algebraic and interaction assumptions. Repeated
multilinear Sumcheck additionally requires protocol calls and repetition in the
checked source profile.

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
ordinary `lean-native` check includes this suite. Executable capacity checks and
logical range/shape premises remain separate; passing these finite comparisons
does not establish universal exporter, native arithmetic or resource correctness.

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
naming rule; helper-internal sites keep their existing namespace.

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
