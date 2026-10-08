# Mathematical composition and capacity

The native path composes bulk numerical kernels inside transparent local bodies,
with total scalar and pairing expressions in the common mathematical IR.
Protocol exchange, transcript actions, relation bindings and terminal decisions
remain visible. All clients lower through participant, exec and physical stages
and execute through the shared Rust runner. There is no protocol-name dispatch.

## Composed clients

| Client | Actual computation and decision | Exercised runtime sizes |
|---|---|---|
| [QAP](../../compiler/test/fixtures/mathematical/qap-composition.mlir) | Bound distinct rectangular sparse A/B/C matrices and assignment; all R1CS rows and ONE/public prefix; inverse/forward coset transforms; numerator contraction by a public G1 query; pairing into GT; received point/target checks | 8, 64, 256, 1,024, 4,096 and 8,192 rows |
| [AIR](../../compiler/test/fixtures/mathematical/air-composition.mlir) | Every trace transition; base-to-ext8 embedding; 2x LDE; opening quotient at zero; even/odd fold under a derived challenge; Merkle commit/open/check at the actual last row | 16, 256, 4,096 and 8,192 rows |
| [GT accumulation](../../compiler/test/fixtures/mathematical/target-accumulation.mlir) | Pairing, target scalar action, bounded loop-carried accumulation, message and independent terminal pairing | 0, 1, 7 and 16 iterations |

Each client uses one compiled deployment per lowering mode for every size. The
normal, unsimplified and storage-release modes all reach the largest size.
The [Rust API client](../../crates/zkc-tools/examples/native_composition/main.rs)
checks actual proof messages against direct Arkworks QAP/pairing equations and
an independent barycentric evaluation for the AIR fold at a challenge derived
from independently encoded invocation roots, origins and observed frames. The
reference checks the echoed challenge against that derivation. A deterministic
context scan exercises rejected ext8 sampler words in the first block; backend
sampler controls own multi-block continuation and exhaustion. It does not
independently authenticate every Merkle path; the QAP reference compares its
MSM/GT frames rather than every proof frame. It records carrier and
proof sizes in `composition-measurements.json`. Normal deployment/program sizes
are 13,252/7,798 bytes for QAP and 25,681/16,273 for AIR; these stay fixed as input
size grows. At 8,192 rows their proof sizes are 262,710 and 33,402 bytes.
These are fixture observations, not performance or security claims.

Controls change the last constraint/transition, witness, public prefix, domain,
query length, root/path/row and terminal data. False equations reject; invalid
coordinates/domains and exhausted quotas stop or refuse under their owning
contracts. Proof truncation and trailing data refuse. Setup-free Merkle leaves
and a structured relation binding exercise contrasting boundaries.

Both clients disclose their full witness/trace. They validate general IR and
runtime composition, not succinctness, hiding, full Groth16 or FRI, or external
proof compatibility. The QAP client intentionally has a verifier that consumes
the matrices. A succinct Groth16 verifier would instead receive a verifying key
and circuit identity. Its computation uses coset **numerator evaluations** with
the prepared query convention; it does not introduce exact quotient division on
an invalid witness. The coset must be disjoint (`shift^n != 1`), each matrix must
have `n` rows, and the MSM query length must equal the numerator length. This
client does not claim that arbitrary imported query bases implement Groth16.

The smallest default QAP/AIR clients also search exact instruction, call,
iteration, live/cumulative value, wire, individual-value, element and group
capacity boundaries for each role. The boundary and one-above probes succeed
with identical proof bytes; one-below repeats the expected capacity refusal.
`composition-measurements.json` retains each boundary and refusal. These are
fixed-provider controls, not monotonicity evidence for arbitrary schedules or
stateful providers.

## Representation choices

- `bn254.gt` is an ordinary group value. `algebra.pairing` is total and lowers to
  `pairing.apply`; G1 and G2 remain ordered, distinct input types. Individual GT
  values support ordinary group operations, data containers, messages and loops.
  Dense GT vectors and batched value-producing pairings remain later extensions.
- Dynamic vector, sparse matrix, group-vector and Merkle data use the complete
  typed native grammar. Existing canonical leaf producers are reused. Structural
  and aggregate preflight precedes allocation and subgroup validation.
- `vector.equal` checks complete columns. Scalar per-row loops over captured
  arrays repeatedly charge those captures against the runner's cumulative value
  budget; this accounting has not changed. Bulk checks avoid that repeated work.
- Formal polynomial expansion remains bounded to 64 explicit interpolation
  points and 100,000 expansion work units. Dynamic domain transforms use compact
  installed kernels in local bodies. No expansion limit was raised.
- Ristretto collections and ext8 matrices share the installed bulk grammar and
  have codec controls; this package adds no full composed protocol consumer for
  those two combinations. Their installation is not a BP+ or zkVM claim.

## Application capacity

`NativeDeployment::with_capacity` and CLI `--capacity=PATH` select operational
ceilings independently of the authenticated deployment, inputs and proof.
Successful proof bytes are unchanged when different ceilings are sufficient.
The CLI reports the effective record, including defaults:

```text
["zkc.native-capacity/2", "elements", "groups", "wire_bytes", "value_bytes",
 ["instructions", "iterations"], ["live_bytes", "total_bytes"]]
```

All entries are canonical decimal strings. The file is at most 4 KiB and has
exact arity; unknown fields or versions refuse. Defaults are 65,536 elements,
4,096 collection/aggregate group points, 16 MiB wire, 64 MiB per value/live
values, a 256 MiB cumulative runtime value charge, one million instructions and
100,000 iterations. Element/group counts may rise to 1,048,576/32,768. Other
ceilings may only be lowered. Numeric elements and group points are counted
across a complete nested message, not separately for each child collection. For
the QAP matrix sequence, the nonzeros across A, B and C share the element ceiling:
three matrices with 25,000 entries each exceed the default 65,536 aggregate
limit even though each matrix fits individually. A host must explicitly authorize 8,192 query
points for the largest QAP client. A zero group collection ceiling does not
forbid an independently decoded fixed scalar group value. Count ceilings do not
promise that many values fit: wire size, retained backing, decode scratch and
live/cumulative budgets all apply. For example, a 32-byte scalar vector reaches
the 64 MiB decoding peak bound before 1,048,576 elements. The 16 MiB invocation
JSON envelope also counts hexadecimal text and duplicated public/data rows.

The selected policy reaches native data loading, backend kernels, setup import,
service registry and runner budgets. Attempts cannot exceed these invocation
ceilings. Signature-only deployment admission uses a dummy default backend;
it loads no invocation payload and grants no capacity. Existing setup/provider
limits and the separately configured external-work ledger retain their owners.
Input admission and runtime execution use separate accounting ledgers: the same
`total_bytes` setting bounds loading work and the cumulative runtime value charge
independently. Canonical public values needed by the selected role are admitted
once and reused after checking exact data-row bytes and physical layout. Other
public values are checked and discarded. These ledgers do not bound total process
memory or combined work across both phases. Byte
preflight for native wire inputs precedes decoding; the loading ledger admits
the decoded value afterward, so a reduced loading ceiling alone does not prevent
a single decode allocation permitted by the backend value ceiling.

The [joint Host](../runtime/bundles.md) uses the same capacity record. The group
quota covers one collection or complete nested message. It is not
a cumulative per-proof subgroup-work bound: many standalone G2/GT messages remain
bounded by proof size and execution limits. Neither this count nor the instruction
budget measures CPU time. A weighted subgroup-work ledger remains a possible
later extension if required by an application.

Lean refuses decoding GT with `reference-pairing-target-unsupported`; its current
kernel reference refuses `pairing.apply` with `reference-kernel-not-supported`
and GT `curve.*` with `group-domain`. Independent binding/type admission is
updated; native execution correspondence and formal security remain separate work.
