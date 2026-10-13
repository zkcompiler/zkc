# Constructed-program Fiat–Shamir verification

## Selected subject and specification

`bridges/constructed/verification.py` checks the actual native constructed
**verifier participant** in a selected mathematical model. It accepts either DSL
`--module NAME=FILE` / `--entry NAME::ENTRY`, or retained `--source FILE`
with an explicit `--policy FILE`. `--candidate FILE` supplies an already retained
candidate for native rechecking; otherwise the driver constructs one. This is
not whole-prover verification.

`zkc.fs-verification-spec/0` has exactly `format`, `source`, `model`,
`experiment`, and `properties`. `source` is a complete explicit
`zkc.proof-request/0`, including contract, source properties/experiment, role,
input bindings, and effect/domain wiring. The checked examples are
`bridges/constructed/requests/schnorr.json` and `sumcheck.json`. These selectors
also work with DSL modules; named DSL security-target resolution is not part of
this schema. Protocol shape alone never selects security intent.

Only `ideal-indexed-transcript/0` is accepted. Registered experiments are:

| Experiment | Required source contract | Property |
| --- | --- | --- |
| `fs.schnorr.fixed-statement-cached-ro/0` | `schnorr.verifier/0` | `knowledge-extraction` |
| `fs.sumcheck.full-prefix-cached-ro/0` | `sumcheck.quadratic-two-round/0` | `false-acceptance-bound` |

Each specification selects exactly its listed property. Unknown fields, versions,
models and experiments, duplicate JSON object members, non-JSON numeric constants,
and oversized/deep JSON are refused. Requests contain no Lean snippets, imports,
tactics, theorem names, alternative primitive meanings or supplied realization
assumptions. The complete source request must select the reviewed source contract
properties. Unsupported inputs produce an unresolved receipt, not a security
counterexample.

## Proof and identity chain

The driver retains the native source, source export, construction policy, candidate,
constructed export, generated Lean certificate, tool invocations/logs and receipt.
For DSL input it checks interface Entry/symbol identity against freshly emitted
retained source. It derives the native policy from explicit prover/verifier roles,
public statement inputs, service input, and challenge/delivery selectors. Supplied
policies must equal that policy. Omitted public statement components are refused.

The following layers must all succeed:

1. Fresh `protocol-lean` export and the existing common bridge's source contract
   certificate, followed by its independent requested-subject check.
2. `protocol-construct-proof` when needed, then `protocol-constructed-lean` on the
   retained source, explicit policy and candidate. The native exporter rechecks
   the candidate against construction from this source and policy.
3. Transparent typed actual constructed syntax, with kernel-checked erasure and
   `snapshot.check = .ok imported`. The full actual `Imported.denote` equation is
   proved under the maintained fixed protocol primitive interpretation. It keeps
   all returned values, stops and live transcript state.
4. The selected security consumer applied to that actual subject. Schnorr derives
   `Realizes` from actual normalization and the independently checked source
   contract. Sumcheck derives its actual `Subject` equation against the complete
   early-stop reference experiment before applying the consumer.
5. Independently reconstructed expected snapshot, metadata, input interpretation,
   public binding/schedule and exact security theorem type. A proposal's chosen
   alias cannot define the expected subject. Admission, full denotation, source
   correspondence and security declarations are checked against that reconstruction.
6. Transitive axiom audit, allowing only `propext`, `Classical.choice`, and
   `Quot.sound`. The driver requires successful Lean exit and every proof marker;
   success text with a failed proof is insufficient.

Common and constructed bridge modules both have a `snapshot.py`. Fixed-directory
module-family isolation prevents one from silently importing the other. Generators
receive disposable copies, while expected-subject rendering retains the original
request and exports. This interface does not sandbox malicious Python code or an
untrusted Lean executable; the maintained renderer and checker are reviewed code.

The receipt hashes exact retained source/candidate files, canonical JSON policy,
policy file, each retained handler body and the complete handler closure,
primitive descriptors, both exports, request, certificate, compiler binary,
maintained formal import sources and bridge implementation files. It also records
toolchain and pinned dependency-manifest hashes. The export's candidate identity
is the native checked canonical generic operation print, distinct from the raw
candidate-file hash; both are retained explicitly. Native parsing/export identity
is a named software boundary, not a kernel authentication theorem.

## Exact conclusions and observations

Schnorr fixes source, construction, application context, full occurrence metadata,
base and public key before the prover runs. Arbitrary adaptive prover queries use
one initially empty cached uniform-field oracle, shared with final verification.
For every total prover with the named `nmaHashQueryBound Q`, the actual acceptance
probability `a` satisfies

`a * (a / (Q + 1) - 1 / card F) <= extractor success`.

The arithmetic is ENNReal with truncated subtraction. `Q` counts prover oracle
calls including repeated keys; final verification adds one. The maintained replay
extractor's counted fresh challenge requests are at most `2 * (Q + 1)`. This is
not a running-time bound or an efficient proof-of-knowledge claim. The witness
relation is `witness • base = key`. The full returned transcript equation precedes
the explicit Boolean acceptance projection; no zero-knowledge or leakage claim
is inferred from that projection.

Sumcheck allows the adversary to choose application context, coefficients, claim
and messages after adaptive oracle accesses. Final verification fixes the selected
source, construction and exact native schedule. Oracle queries may use any binding,
including inconsistent and out-of-order full prefixes. The second query keeps the
first delivered challenge. Under `IsTotalQueryBound adversary Q`, actual false
acceptance is at most `(Q + 3) * (2 / card F)`. The actual adversary-plus-verifier
process uses at most `Q + 2` oracle calls; the conservative bound additionally
accounts for one reduction preparation query. The event is actual acceptance
and a claimed sum unequal to the polynomial's Boolean sum.

The native Sumcheck game retains the full execution record, reached query log and
returned transcript before observing acceptance. Early rejection need not have
the same final cache, transcript or cost as completed replay. Acceptance coupling
does not authorize exposing discarded state to an attacker or reusing an
acceptance-only equation as a contextual state equivalence. No independence is
inferred from separate service handles.

## Model boundary and receipts

The retained native descriptor is `merlin3.bls12-381.fr64be/0`, with
`zkc.framed/0` framing. Its selected **ideal interpretation** is conditional:
concrete Merlin/provider security, byte encoding/codec conformance, host transcript
initialization, native arithmetic/lowering/runtime correctness and compiler
correctness are not established. The theorem uses a mathematical finite field
(and a compatible additive group/module for Schnorr); it does not certify native
BLS operations. Public binding and occurrence metadata are typed model data, not
a proof of injective native serialization. The adversary query budget remains an
explicit quantified premise.

`zkc.fs-verification-receipt/0` starts as `unresolved`, invalidating any stale
success before full CLI argument validation, reading a request or running tools. Only all completed proof layers
can change it to `verified-in-model`. Failure, unsupported input, missing imports,
incorrect theorem type, forbidden axioms, timeout or tool failure leave no verified
properties. Exact output options are recognized before full argument parsing, so
invalid later CLI options cannot preserve an old success. Concurrent invocations
on one output directory are refused with `output-busy`; the contender reports
failure on stdout and leaves the active owner's evidence untouched. Each owned
invocation checks a fresh private read-only certificate path, rechecks proof and
retained subject bytes before success, and only then publishes the convenient
`Certificate.lean` copy and atomic receipt. The receipt records its invocation
and private certificate path. The output lock coordinates this driver; it is not
a sandbox against a process with arbitrary filesystem write authority.

Receipts enumerate discharged layers, exact query conclusion and
remaining boundaries. They are reproducibility records, not signed proof objects
or runtime authorization. Recheck certificates with the recorded implementation,
formal source closure and pinned dependencies.

For example, from the repository root (with the current exporter built):

```sh
python3 lean/bridges/constructed/verification.py \
  --spec lean/bridges/constructed/requests/schnorr.json \
  --module schnorr_forms=lean/bridges/common/fixtures/schnorr-forms.zkc \
  --entry schnorr_forms::Helpers --compiler build/compiler/zkc-compile \
  --output build/experiments/fs-verification/schnorr
python3 lean/bridges/constructed/security_check.py \
  --compiler build/compiler/zkc-compile \
  --output build/experiments/fs-verification/security-controls
```

The driver builds its selected maintained imports, then checks the generated
certificate with `lake env lean -DwarningAsError=true` in the optional ArkLib
integration. `--lake` selects the trusted toolchain executable; `--timeout` bounds
each invocation (positive, finite, at most 1200 seconds). Timeout kills the
complete child process group. Native/exporter controls remain owned by
`bridges/constructed/check.py`; `security_check.py` exercises the four supported
source forms and the false-receipt authority boundaries of this pipeline.
