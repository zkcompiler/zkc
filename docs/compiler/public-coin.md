# Public-coin verifier views

The native analysis asks which actual verifier values determine its guards and
decision, and which values precede each public challenge. The
[profile](../spec/profiles/compiler/public-coin.md) owns the judgment and formats.
It derives a bounded view from existing MLIR SSA and action order. There is no
second mathematical graph or new IR stage.

## Motivating counterexample

Static composition made a concrete transformation comparison possible. The
public-table Sumcheck binds both tables and its claim. The composed R1CS client
also reads the verifier's assignment, including coordinates absent from its
public statement. A transformation must account for those values.

Consider a relation with columns `(ONE,w)` and contradictory rows `w = 1` and
`w = 2`. Its residual is `(w−1,w−2)`. Weighting by `tau` gives

```text
(1−tau)(w−1) + tau(w−2) = w−1−tau.
```

A transform computing `tau = H(empty statement)` before fixing
`w` lets a prover supply `w = 1+tau`; the weighted Sumcheck then accepts. The
current interactive experiment fixes the verifier's assignment before drawing
`tau`. For each fixed `w`, the displayed bad event is one field point under a
uniform draw. This is a counterexample to statement-only transformation, not a
new defect in that interactive experiment or a bound on all malicious strategies.

The analysis refuses statement-only binding for this client. Full-assignment
binding passes and reports the non-statement witness port. Binding is a declared
view premise: the report does not publish, authenticate or hash that witness.
A noninteractive construction using this client must fix the required values
before deriving the affected challenge.

## Alternatives considered

| Candidate | Decision and reason |
|---|---|
| Explicit transcript transformation | Selected in the [native proof design](native-proofs.md): analyze retained common source, emit role-local affine calls after projection, and admit exact host-created transcript resources. Selected construction and independent execution are implemented under the native proof policy. |
| Pure deterministic derivation on role-family values | Not selected as the execution representation. It does not preserve affine custody, stopped prefixes or transition accounting by itself. A suite-specific mathematical interpretation can still support later analysis. |
| Verifier-view analysis | Implemented at the bounded scope below. It detects missing actual input binding on existing clients and changed challenge edges in synthetic controls; it specifies the values a construction must account for. |
| Algebraic completeness/special soundness | Defer until a client needs an interpreted relation ideal or a two-transcript extraction experiment. Existing scalar Schnorr examples and exact Sumcheck correspondence do not supply that extractor experiment or imply those analyses. |

Typed SSA carries mathematical dependencies; explicit exchanges and query
order carry interaction. Per-verifier receive anchors retain the values that
the verifier actually observes in the same program.

## Implementation boundaries

`ZkcCompiler` owns the analysis because it invokes the existing preparation
workflow. `createPrepareProtocolPass(false)` exposes unsimplified expansion;
projection and default preparation retain their existing behavior. An owned
clone, ordinary admission, shared role availability and registered operand
contracts supply the analysis inputs. Reports use numeric dependency anchors
and prefix lengths to avoid copying each growing transcript.

The independent requirement pins entry ports and ordered query/delivery sites.
The implementation discovers the actual edges. It refuses hidden V-local calls,
unmatched or changed coins and omitted verifier dependencies. Report checking
recomputes everything. Checked compilation binds the result to the source text
and exact emitted bundle, while preserving the narrower structural claim.

## Adopted construction boundary

The [native proof profile](../spec/profiles/compiler/native-proofs.md) fixes the
selected independent execution and construction boundary. The [single policy](native-proofs.md#policy-and-formats)
covers flat, iterated, committed and structured clients. Broader automatic
derivation and new security theorems remain separate work. This public-coin report
keeps its existing meaning and does not itself authorize the construction.

Preserve the [observation analysis inputs](ir-foundation.md#information-retained-for-observation-analyses)
through construction. The existing public-coin report does not cover
general algebraic observations, root distribution laws, later disclosure or
prover behavior. Its verifier receive anchors must not become honest sender
expressions without an explicit premise. Implementing an affine observation
analyzer is separate from retaining these inputs and from placement correctness.

Construction checks source draw/delivery pairing, complete public bindings and
actual candidate operands against the retained source. It then threads explicit
state in each projected role, avoiding a new common role-family assembly
operation. The construction supplies authorized public values to the host
for transcript-root initialization and adds no participant data inputs. Private
verifier inputs are not silently disclosed. Iterated prefixes and local public replay
recipes require extensions beyond the current static report. Diagnostic sites
and generated helper names do not define cryptographic occurrence identity.

[Merlin's transcript operations](https://merlin.cool/transcript/ops.html) are a
concrete labeled/framed API, not a theorem for arbitrary native clients.
[Round-by-round soundness research](https://eprint.iacr.org/2019/1261) and the
[duplex-sponge Fiat–Shamir analysis](https://eprint.iacr.org/2025/536) have distinct
models and premises. Select and state the relevant claim before implementing a
concrete construction. A structural checker, hash implementation and security
argument remain separately reviewable results.
