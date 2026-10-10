# Original-source artifact reference

`artifact-reference` is an optional Lean interpreter for the source and
construction records defined by [`Tools.Artifact`](../../Tools/Artifact/Main.lean).
It interprets the original generic library or common protocol's validator under
its selected transcript construction. These records are independent of the
supported `zkc.program/0` carrier; this tool is not a native proof Host or a
validator of the current compiler's output.

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
implements its own construction interpretation without calling the compiler or
native Runner. `ExceptT` outside `StateM` preserves the reached cursor,
events and consumed oracle answers on failure. An exception cannot silently reset
the run to an earlier successful prefix.

Lean implements source control, Fr and Ristretto-scalar arithmetic, finite vectors,
univariate polynomials and BLS table operations independently.
Public SHA-256, Merlin and group/PCS computations enter as explicitly supplied
replies. Each request contains the actual configured key and public operands,
or the binding root and complete transcript history. Requests retain full
nominal types and explicit operation static arguments. Suite-bearing Merlin
requests expect raw 64-byte output; Lean performs the corresponding field
reduction. Values retain the nominal field/group distinction; another domain
requires an explicit interpretation, not nominal erasure.

Replies are keyed by the **entire request**. Duplicate or unused supplied
replies refuse; a missing request remains explicit and can be answered before
retrying. There is no ordinal acceptance tape or witness-table oracle. Reply
correctness is a trusted cryptographic premise.

## Use

From `lean/`, after preparing the pinned Lean dependencies:

```sh
lake build artifact-reference
.lake/build/bin/artifact-reference identity SOURCE DESCRIPTOR
.lake/build/bin/artifact-reference reference SOURCE DESCRIPTOR INPUTS PROOF REPLIES
```

`SOURCE`, `DESCRIPTOR`, `INPUTS` and `REPLIES` are files in the tool's own JSON
formats; `PROOF` contains candidate bytes for that modeled construction.
[`Inputs`](../../Tools/Artifact/Inputs.lean) defines preparation and reply decoding;
[`Main`](../../Tools/Artifact/Main.lean) defines the command interface. The identity
command inspects normalized construction identity for this model, not the native
program's identity policy. It optionally accepts a configuration file.

The reference command optionally takes a final transcript-transition budget,
defaulting to 100,000. It accepts at most 32,768 supplied reply records; inputs
and proofs are bounded at 16 MiB and reply files at 64 MiB. JSON preflight checks
the string/array grammar and depth before parsing. These are independent tool
limits, not promises about native Host exhaustion.

The observation reports outcome, ordered public source events, consumed proof
bytes, selected challenge count and pending public requests. Missing replies
remain visible; the command does not resolve them through a native service.

## Assurance distinctions

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| Existing typed projection theorems | Source-role and target meanings agree for their typed grammar and hypotheses | Native JSON elaboration or C++ construction correctness |
| Concrete `interactive-protocol --check` | A candidate in the tool's portable format matches its common subject under the checked physical contract | Current MLIR/program correspondence or original-to-constructed semantic preservation |
| `Zkc.Realization.Framing` | Bounded length framing separates list-byte payloads and preserves an appended suffix | Correspondence with the executable ByteArray/native cursor |
| [Artifact controls](../../Tests/ArtifactReference.lean) | Model-specific admission, failure prefixes and byte/field examples | Native correspondence, backend verification or cryptographic security |

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
and resource premises explicit. No native comparison route is provided here.

The count-one result limitation requires a representation/control decision
before transforms depend on it.
PCS key identities have application-owned input/receive
associations and explicit failure prefixes. Exact zero-trip receives are excluded
from that executable policy; the independent source traversal never needs native
inactive-instance names. Nested dynamic visits to one source receive still share
one selected setup in this CLI. Streaming observations and general physical
resource accounting require further work before large-run exhaustion equivalence
can be claimed.
These are separate extensions, not missing hypotheses to silently assume today.
