# Original-source artifact reference

`artifact-reference` is an executable Lean consumer for the concrete
[artifact profile](../../docs/compiler/artifact-format.md). It interprets
the original generic library or common protocol's validator under the selected transcript
construction. It does not read the compiler's generated common/participant code.
The [execution guide](../../docs/compiler/artifact-execution.md) places it
beside native compilation and the separate participant checker.

## Module responsibilities

| Module | Role |
|---|---|
| `Tools.Artifact.Bindings` | Independent generic preparation and full nominal admission for the finite installed domains |
| `Tools.Artifact.Configuration` | Original source-port key authorization and receive selections under fixed public loop counts |
| `Tools.Artifact.Transcript` | Exact Merlin domain/label/call encoding, shared with the interactive reference |
| `Tools.Artifact.Descriptor` | Parse construction selection; admit source roles, public bindings, selected draw authority and public-artifact profile |
| `Tools.Artifact.Codec` | Canonical field/public values, bounded proof cursor, logical trees and occurrence encoding |
| `Tools.Artifact.Runtime` | Values, state, ordered events, exact public oracle requests, arithmetic and retained failure state |
| `Tools.Artifact.Interpreter` | Original protocol calls, counted loops, local computations, messages and selected challenges |
| `Tools.Artifact.Inputs` | Application context, public/configuration coverage, exact setup checks, binding root, actual acceptance result and EOF |
| `Tools.Artifact.Main` | Bounded command input and JSON observations or pending public requests |

The consumer reuses `Tools.Interactive` source decoding/admission and types. It
implements construction interpretation independently of C++ recipe emission and
native Runner execution. `ExceptT` outside `StateM` preserves the reached cursor,
events and consumed oracle answers on failure. An exception cannot silently reset
the run to an earlier successful prefix.

Lean implements source control, Fr and Ristretto-scalar arithmetic, finite vectors,
univariate polynomials and BLS table operations independently.
The `artifact-primitive` Rust service supplies public SHA-256, Merlin and
group/PCS computations using pinned upstream libraries. A request contains the
actual configured key and public operands, or the binding root and complete
transcript history. `/2` requests retain full nominal types and explicit operation
static arguments. Its suite-bearing Merlin service returns raw 64-byte output;
Lean performs big-endian reduction to Fr or little-endian reduction to the
Ristretto scalar field according to the exact suite. Values retain the nominal
field/group distinction; another domain requires an explicit interpretation,
not nominal erasure. Replies are keyed by the **entire request**. Duplicate or
unused supplied replies refuse; a missing request remains explicit and can be
evaluated and retried. There is no ordinal acceptance tape or witness-table
oracle. This service is a trusted public cryptographic boundary, not a proved
implementation or a protocol-specific verifier.

The native diagnostic representation `zkc.diagonal-observation/1` exposes a
view's typed factors and backing. It is not a canonical transcript value. Exact
dense observations and interpreted physical observations are reported separately.

## Use

Build with `lake build artifact-reference interactive-protocol` in `formal/`
and `cargo build -p zkc-tools --bin artifact-primitive` at repository root.
The [reference driver](../../tests/support/run_reference.py)
resolves exact pending requests and retains inputs/replies/observations:

```sh
python3 tests/support/run_reference.py --help
```

The optional `--transcript-budget` on the Python driver (final positional argument
on the Lean executable) selects the same transition-count budget as the native
host. The default reference budget is 100,000; comparisons pass their native
budget explicitly.

Comparison tools also impose finite ceilings: 4,096 public requests per driver
run, 32,768 supplied reply records in Lean, and 200,001 explicit Merlin calls per
`/3` service request. Inputs and proofs are bounded at 16 MiB and reply files at
64 MiB. JSON preflight accepts only strings/arrays and checks depth before parsing,
including for larger input/reply files. These are reference-tool limits, separate
from the native host's `u64` transcript budget. Exceeding them refuses or stops
the comparison driver; it never establishes a native protocol outcome.

The final observation reports outcome, ordered public source events, consumed
proof bytes and selected challenge count. Comparisons include rejection and
malformation, not only honest acceptance. Native host input/observation budgets
and the Lean interpreter's finite evaluation policy have different engineering
roles; universal exhaustion equivalence is not established.

## Assurance distinctions

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| Existing typed projection theorems | Source-role and target meanings agree for their typed grammar and hypotheses | Native JSON elaboration or C++ construction correctness |
| Concrete `interactive-protocol --check` | The supplied participant artifact matches the constructed common subject under its checked physical contract | Original-to-constructed semantic preservation |
| `Zkc.Realization.Framing` | Bounded length framing separates list-byte payloads and preserves an appended suffix | Correspondence with the executable ByteArray/native cursor |
| Original-source/native differential execution | Exact outcomes, events, cursor and draws agree for retained concrete runs | A theorem for all source programs, inputs or hostile proofs |
| Public primitive checks and key codecs | Actual upstream computations, request specificity and tested serialization/refusal behavior | Backend FV, honest setup, constant-time arithmetic or cryptographic security |

The existing interactive Sumcheck soundness theorem does not automatically transfer
to this Merlin construction. A future FS theorem needs a precise interactive
relation, adversary/oracle model, sampler, composition rule and concrete adapter.
ArkLib/VCVio can supply such theorem components when their exact hypotheses and
admitted gaps are accounted for; this executable reference imports no implicit FS
security result from either library.

## Follow-up research

Before broadening a correctness claim, connect the original-source interpreter
to typed construction/recipe laws and prove the concrete framing implementation
correspondence. Keep public agreement, successful guard prefixes, stateful effects
and resource premises explicit. Independent differential tests remain the practical
native connection adopted for the current compiler.

The count-one result limitation requires a representation/control decision
before transforms depend on it.
PCS key identities have application-owned input/receive
associations and failure-prefix comparisons. Exact zero-trip receives are excluded
from that executable policy; the independent source traversal never needs native
inactive-instance names. Nested dynamic visits to one source receive still share
one selected setup in this CLI. Streaming observations and general physical
resource accounting require further work before large-run exhaustion equivalence
can be claimed.
These are separate extensions, not missing hypotheses to silently assume today.
