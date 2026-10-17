# Native participant comparison

`participant.py` compares original structured participant replay with actual
compiler-produced endpoints executed by Rust `Runner`, `NativeBackend`,
`ServiceRegistry`, and native wire codecs. The maintained initial subjects are
`example::Interactive` from the Schnorr library and the existing
`open-services.mlir` fixture. This is bounded executable evidence, not Rust
refinement or a security theorem.

## Run and retain evidence

Build the compiler, the `structured-source` Lean executable with open replay,
and the test-only driver using the pinned workspace dependencies:

```sh
cargo build --locked --release -p zkc-test-drivers --bin participant_correspondence
python3 lean/bridges/structured/participant.py \
  --compiler-revision="$(git rev-parse HEAD)" \
  --lean-revision="$(git rev-parse HEAD)" \
  --report=build/reports/lean/participant/run-1/report.json
```

The shared structured `Suite` owns report publication, command records, source
archives and tool retention. Each invocation first replaces the selected status
with `running`, then allocates a fresh immutable run directory. Setup failure and
interruption replace that marker with failure; a prior run's archives and tools
remain unchanged. `participant.json` is additional per-run observation detail,
referenced by the shared report. Reusing the selected report path is supported.
Explicit `--compiler`, `--optimizer`, `--reference`,
`--lean`, and `--native` paths select existing executables. `--compiler-source`
and `--lean-source` select their source roots when these differ from the checkout;
the corresponding full revisions must match those roots. The operator supplies
the build-source association. The report retains those working source archives,
including dirty files, and their status; it does not establish binary derivation.
On hosts coordinating other studies, put builds and the entire command under
`flock -n -E75 /tmp/zkc-benchmark-execution.lock`; exit 75 means defer, without
holding an idle lock. Set and retain thread/affinity policy for the host.

The companion subclasses the structured bridge's maintained `Suite` and reuses
its `evidence.py` atomic reports and source archives. It copies and hashes all five executables before execution,
retains exact commands, stdout/stderr (including failures), start/end times,
affinity and thread settings. Authored module bytes, original MLIR, complete
snapshot, checked projection, physical subject, exact bundle candidate, options,
requests and observations are retained. Hashes identify compared bytes, not
correct transformations. Missing tools, failed subprocesses and malformed
reports are `HarnessFailure`; unsupported observer/type/control coverage is
`Unsupported`; differing observations are `Mismatch`. Only `Pass` contributes
to passing coverage; a suite with unsupported cases exits unsuccessfully.

## Binding and value relation

The compiler emits the actual `.zkc` Interactive entry. A full re-export binds
the structured snapshot to the original source bytes. The projection pass checks
actual source operands and participant projection. The companion reads original
input/service/output indices from that retained projection, checks source scopes,
and lowers that same subject to a candidate equal to the bundle's candidate.
Rust independently admits those exact bytes and checks participant, role, types,
port arities and original query roots. A role-local service index is composed
with the projection's ordered original ingress indices. Generated names are
never decoded to guess a source index.

Each role has its own complete source-indexed input list. Public inputs and
received values remain independent. No witness relation or honest delivery is
assumed. The companion uses source replay to obtain expected sends and outputs;
it contains no Schnorr arithmetic evaluator. Lean and the C++ original-SSA
reference are compared at each observed prefix and on completion.

The executable Lean model interprets group values as additive scalar labels.
For a sampled label `a`, the native relation is the actual BLS12-381 point `aG`.
The probe compares native points directly to these mapped labels and retains
both canonical native wire encodings. It never extracts discrete logarithms.
The expected mapping and native group kernels share the installed group library;
these tests therefore do not independently prove group implementation
correctness or decoding of arbitrary points. Scalar/group zero, identity and
modular wrap cases exercise this sampled relation.

## Prefix and residual observations

At every action the probe retains the full native origin/cut, source request,
provider state, frame/resource counts and native ledgers. Three repeated polls
must preserve the pending action and state. A wrong session cut must be refused
without advancement; a consumed cut must become stale. The same live runner
continues through subsequent actions. Native nested occurrence paths are retained;
nonempty paths are currently unsupported by this source comparison.

A source replay's missing-reply `incomplete` is translated only when its final
records show an unanswered request. It means a pending native observation. An
explicit script `incomplete` reply is not translated. Prefix-only runs retain
state before host cancellation and after cleanup. Returned values remain in the
Runner ledger after frames and leases close; cancellation and stops release
values. Native allocation/work limits remain separate from source observer
capacity and are recorded, not identified with source steps.

The following adapters are deliberately narrow:

| Source observation | Native observation and extra obligation |
|---|---|
| Script `abort` at an exposed action | Checked native `Cancelled` with the same origin/role and no native instruction site, before consumption; source site comes from the retained pending cut |
| Script `exhausted` for draw | Only native `exhausted:resource-budget` or `exhausted:test-tape`; incremented generation/draw count, remaining budget, poison, known completion and released lease checked |
| Script `refused` for injected bad provider reply | A real draw first, then test-only wrong reply type; `runtime-contract:Payload`, poison and retained consumption checked |
| Script `refused` for completed malformed receive | Actual codec `Invalid` reason supplied to `complete_receive`; exact terminal `Decode(reason)`, origin, role and accepted site checked; consumed cut becomes stale |
| Source guard stop | Native explicit stop with the same reason and site |
| Ordinary `false` | Returned Boolean, distinct from every stop |

Codec preflight failure by itself preserves a pending receive. A wrong typed
`complete_receive` argument is an API refusal with the same pending state. The
probe then either continues with a valid canonical payload, or submits the
actual decoder failure as an accepted completion. Wrong lengths, noncanonical
scalar/group encodings, the scalar modulus and noncanonical infinity are
covered. Attempt completion and the adapter's payload retention obligation are
recorded explicitly; the driver does not claim to observe a joint Host payload
slot. Fault modes have a closed action/type vocabulary and each requested
injection must be applied exactly once. Invalid or unreached injections are
`HarnessFailure`.

The existing generic service fixture tests alias versus distinct roots, guard
failure, exhausted budget, exhausted tape and malformed post-consumption reply.
The registry's authentic `same_root` relation supplies the alias matrix. State
checks cover lifecycle stage, generation, logical draws, budget, poison,
completion knowledge and lease status. Reacquisition must preserve state and
refuse poisoned roots specifically with `refused:service-poisoned`. These operational observations supplement source replay;
the source process alone does not specify registry cleanup or poisoning.

## Controls and limits

Both Schnorr roles cover honest execution, independently changed public copies,
each altered receive, zero/identity/wrap, pending and cancellation at each action.
The companion changes actual source arithmetic, copies provenance into an
admissible changed snapshot, and checks that source binding rejects it. Executing
the newly compiled changed source against the old expectation must reach an
unequal actual/mapped value, retaining both encodings and a `value-relation`
reason. Unsupported execution, harness failure and unrelated binding mismatches
cannot satisfy this arithmetic falsification control.
Changed event values/sites/roots, projection roots and provider residuals are
negative controls, alongside explicit unsupported and harness-failure controls.

This package adds no production kernels, IR changes, source semantics, native
Lean interpreter or theorem about Rust. It observes open endpoints under an
explicit host policy; it does not prove the joint scheduler. The importer supports
retained protocol repeats, but this participant suite does not yet supply the
source/reply/provider cases for multilinear Sumcheck. The checked projection reader accepts a deliberately
small current printed interface; unfamiliar forms fail closed. The driver
request envelope (`zkc.participant-probe/0`) embeds the existing
`zkc.structured-open-request/0` and expected result, plus projection binding,
provider plan, optional fault and session. Malformed binding shapes, out-of-range or duplicate indices and expected output
arity errors are driver `HarnessFailure`, before native execution. Its observation envelope is
`zkc.participant-observation/0`; the additional participant detail is
`zkc.participant-comparison/0`. The selected report retains the shared
`zkc.structured-comparison/0` format. These are test evidence formats, not runtime IRs.

This driver depends on the combined structured open importer and its maintained
report lifecycle. It imports and subclasses that owner directly. A copied
executable from an active build is not evidence that it reflects the latest
uncommitted source. Retain its hash and require a fresh integrated build before
reporting current-source joint validation.

Before selecting terminal status, the driver checks both its working source
archive and each explicitly selected compiler/Lean build-source archive for
changes. The participant detail and shared report receive the same status,
including source failures and handled publication errors. The shared report
retains the hash of the final participant detail. As with the shared lifecycle,
a permanently unwritable destination or uncatchable termination may prevent
publication; an archive alone does not prove executable derivation.
