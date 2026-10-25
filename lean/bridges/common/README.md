# Native common-source bridge

This optional bridge connects retained common PIR to the independent Lean
model. It requires the native compiler, a separately implemented native SSA
reference, and the Lean `common-source` executable. It is outside the default
standalone Lean checks.

From the repository root in the pinned development environment:

```sh
cmake --build build/compiler --target zkc-compile zkc-common_reference-test -j 4
(cd lean && lake build)
python3 lean/bridges/common/check.py \
  --report build/experiments/common-source/report.json
```

The runner copies the selected executables for a stable run and records their
hashes, the seed and source identities. `--compiler`, `--reference`, `--lean`,
`--seed` and `--cases` select explicit inputs. Failures retain their native text,
export and request beside the report. Successful temporary inputs are removed;
the deterministic seed and checked-in fixtures reproduce them.

The suite regenerates the closed Schnorr protocol and an unrolled two-round
quadratic Sumcheck DSL fixture. It checks their complete exported snapshots and
generated Lean constructor data. Six additional exports cover helper-based and
algebraically rearranged implementations plus early-challenge and wrong-residual
controls. `contracts.py` compares the three positive verifier forms per protocol
on shared replies and intentional guard/terminal branches; it also checks that
the negative sources differ as predicted by their Lean refutations.
It also exercises repeated mathematical helper
calls, rearranged two-layer scalar folding, an AIR-style residual, and generated
three-role graphs. Cases retain all definitions, including unused ones.

Each role runs against the same explicit inputs and replay prefix in two
implementations. The C++ reference interprets original SSA directly; it does
not consume the exported descriptors. Lean elaborates those descriptors and
runs its independent semantics. Comparisons include actual request order,
service handles, sent values, returned components, every stop reason, consumed
replies and events. Replay prefixes explore arbitrary replies and request
substitution. Sumcheck controls distinguish honest success, rejection before a
challenge, and a false terminal result after valid boundaries.

A deliberate addition-to-subtraction mutation must be detected. Its control
removes unused native definitions and reduces inputs while rechecking native
admission, leaving a one-operation counterexample. This is a bounded greedy
shrinking control, not a general minimal-counterexample theorem.

The field and additive group use **Z/97** in both references. These comparisons
check the selected scalar PIR interpretation, not production BLS12-381 kernels,
four lowering stages, Rust execution, real randomness or full FRI/STARK security.
See [the supported connection boundaries](../../docs/support.md).

## Constructor data

`snapshot.py INPUT.json OUTPUT.lean --namespace NAME` renders transparent
constructor data. It does not synthesize a security theorem. The fixture bridge
checks exact regeneration; Lean separately checks admission and program proofs.
Refreshing a source fixture requires reviewing changed correspondence, not just
replacing a hash to obtain a passing test.

[Schnorr](../../ZkcExamples/NativePrograms/Schnorr.lean) and
[Sumcheck](../../ZkcExamples/NativePrograms/Sumcheck.lean) are concrete clients.
Variant clients [reuse their contracts and property theorems](../../docs/architecture.md#reuse-and-composition).
Their positive proofs are for arbitrary
fields/modules under stated hypotheses, rather
than exhaustive checks of Z/97. Explicit proof requests automate bounded
correspondence and registered property application; arbitrary-source theorem
selection is outside that profile.

## Explicit proof requests

A request supplies the intended contract, mathematical experiment, properties,
public-input binding and effect wiring. The tool generates proofs for that
choice; it does not infer a security claim from a protocol name. See the
[request and receipt contract](../../docs/spec/verification.md).

From the repository root, after building Lean and the native compiler:

```sh
python3 lean/bridges/common/verify.py \
  --module factor_openings=lean/bridges/common/fixtures/factor-openings.zkc \
  --subject factor_openings::HornerProtocol \
  --request lean/bridges/common/requests/factor-openings.json \
  --output build/experiments/proof-request
```

Alternatively, use `--snapshot lean/ZkcExamples/NativePrograms/fixtures/factor-horner.json`
in place of `--module` and `--subject`. `--module NAME=PATH` is repeatable for
multi-module sources. `--compiler` and `--lake` select explicit tools.

A successful receipt says `verified-in-model` and lists each property and its
premises. `Certificate.lean` contains admission, imported-to-symbolic process
equality, source-to-contract equality and the property terms. Lean checks the
candidate and audits its transitive axioms. A separate request interpreter checks
that this contract concerns the admitted source's actual denotation with the
requested inputs and wiring, then derives the reported `ExpectedRequest`
properties. `lean.log` records both checks. The parser, constructor renderer and
request interpreter remain reviewed, tested parts of the tool.
Unknown claims, incompatible experiments, wrong bindings, unproved equalities
and proof-budget failures produce `unresolved` receipts and a nonzero exit.
A copied hash or a printed success marker cannot replace a proof.

`registry.py` owns reviewed contract descriptions and independent property
consumers. `symbolic.py` proposes typed source syntax and selected-role processes.
`candidate.py` restricts these expressions to pure constructor and scalar syntax;
the reviewed renderer owns every Lean command, proof script and audit. Generator
inputs are disposable copies, separate from the checker and receipt subjects.
The proposed expressions are untrusted; Python execution, the validator, renderer,
registry and selected toolchain remain trusted. Explicit syntax avoids repeated
dependent-type checking through the importer. `Snapshot.check_parts` still requires all admission checks
and equality to the actual elaboration. The correspondence proof normalizes pure
algebra while retaining effects, arbitrary replies, guards and stops. This is a
bounded partial evaluator and equality procedure, not a general theorem search.

The three registered contracts cover Schnorr, two-round quadratic Sumcheck and
Sumcheck followed by public factor openings. Completeness and soundness properties
reuse one implementation certificate per source. Adding a supported source form
does not add another security argument for every property. New cryptographic
experiments still require proved consumers and their real premises.

Run the source/property matrix and refusal controls with:

```sh
python3 lean/bridges/common/verify_tests.py \
  --output build/experiments/proof-request-matrix
```

It includes a newly compiled source with renamed module/protocol/sites and
reordered inputs, stale bindings, changed equations/effect order, a copied
positive identity, unsupported PCS/Fiat–Shamir claims, incorrect coin models and
deliberately corrupted expression candidates, commands and comments in proposals,
changed generator inputs, valid expressions for a different program, proof-budget
exhaustion and JSON parser bounds. Its report counts `verified_requests`, one
per verified request rather than per distinct source, separately from property
instances and unresolved controls. The ordinary bridge additionally
checks expanded/Horner composed sources, both opening failures, wrong points
and residuals, and stopped prefixes at every reached action. These executions
use Z/97; symbolic certificates quantify over the stated fields/modules.

Generated maintained factor clients are reproduced by `verify.render_client`
from their JSON exports and explicit request. The ordinary bridge checks them
byte for byte. Editing a request or generator requires regenerating these clients
and rechecking admission, correspondence, property terms and controls.

## Authored targets and external consumers

The named `--spec` path resolves an existing DSL `spec` target through the native
interface and separately imports its relation formula. The current scalar
Schnorr/discrete-log adapter proves the formula correspondence and connects two
accepting actual verifier transcripts to a witness accepted by that authored
relation. `requests/schnorr-dsl.json` shows the required named roles, inputs,
service, target, contract and experiment. An opaque or different relation requires
another proved adapter. The schema is defined in the
[verification specification](../../docs/spec/verification.md).

`requests/schnorr-simulation.json` selects VCVio honest-verifier simulation;
`requests/sumcheck-arklib.json` selects ArkLib interactive soundness. Build the
optional security package before using these requests. The same consumers work
for original, helper-based and reordered/Horner source forms.

```sh
python3 lean/bridges/common/intent_tests.py \
  --compiler build/compiler/zkc-compile \
  --output build/reports/lean/intent
```

These controls include false relation bodies with the expected names/selectors,
wrong-relation certificates, wrong target operands, explicit refusal diagnostics,
and external consumer reuse. Reader refusal controls require exit status 1 with
the expected diagnostic, and request controls require the expected receipt code;
a crash or signal termination never counts as a refusal. Generic extensions can use the typed Lean
`Certificate`/`Consumer` API without changing this bounded registry.
