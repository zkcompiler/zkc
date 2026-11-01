# Public-coin verifier views

The native analysis asks which actual verifier values determine its guards and
decision, and which values precede each public challenge. The
[profile](../spec/ir/public-coin.md) owns the judgment and formats.
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
| Explicit transcript transformation | Selected in the [native proof design](construction.md): analyze retained common source, emit role-local affine calls after projection, and admit exact host-created transcript resources. Selected construction and independent execution are implemented under the native proof policy. |
| Pure deterministic derivation on role-family values | Not selected as the execution representation. It does not preserve affine custody, stopped prefixes or transition accounting by itself. A suite-specific mathematical interpretation can still support later analysis. |
| Verifier-view analysis | Implemented at the bounded scope below. It detects missing actual input binding on existing clients and changed challenge edges in synthetic controls; it specifies the values a construction must account for. |
| Algebraic completeness/special soundness | Defer until a client needs an interpreted relation ideal or a two-transcript extraction experiment. Existing scalar Schnorr examples and exact Sumcheck correspondence do not supply that extractor experiment or imply those analyses. |

Typed SSA carries mathematical dependencies; explicit exchanges and query
order carry interaction. Per-verifier receive anchors retain the values that
the verifier actually observes in the same program.

## Implementation boundaries

`ZkcAnalysis` owns the immutable module-level numerical and protocol observation
analyses. `ZkcCompiler` selects the subject and produces the checked report.
An authored view reads original Protocol IR; a realized view reads the actual
candidate and generated-exchange associations from the checked realization owner.
Checked compilation reuses that owner. Standalone analysis prepares and realizes
once under independently supplied mathematical and oracle policies.

Shared definitions and repeat-body summaries retain actual SSA substitutions,
role-relative observations, logical stops, exact query origins and ordered pending
challenge transfer. Repeat carries use a bounded fixed point including zero trips;
iteration maxima are not unrolled. Actual deterministic numerical helpers are
summarized through scoped execution and installed primitive contracts. Unknown
effects or unsupported control refuse. A dependency never proves that an encoding
is injective or that a value is cryptographically bound.

The independent requirement pins the subject, complete deployment entries,
verifier data ports and ordered query/delivery selectors. All verifier data inputs
must be accounted for, even when unused; source statement membership is recorded
separately. Field draws, scalar `UniformIndex` and product `UniformIndices` retain
distinct laws and exact static domains. Generated deterministic oracle requests
are recognized only through checked source/candidate associations.

Reports retain a bounded definition DAG, body identities, primitive premises,
full realization and independent policy selections. Rechecking recomputes the
complete view. Checked compilation also pins source text, exact emitted bundle
and the remaining stages from the analyzed subject. There is one current `/0`
schema, with no flat-report reader. See the [protocol observation contract](../spec/ir/protocol-observations.md)
for ownership, invalidation and transfer rules.

## Adopted construction boundary

The [native proof profile](../spec/formats/proof.md) fixes the
selected independent execution and construction boundary. The [single policy](construction.md#encoding-and-message-semantics)
covers flat, iterated, committed and structured clients. Broader automatic
derivation and new security theorems remain separate work. This public-coin report
keeps its existing meaning and does not itself authorize the construction.

Preserve the [observation analysis inputs](pipeline.md#analysis-boundary)
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
verifier inputs are not silently disclosed. Structured iterated prefixes and
checked deterministic request replay are supported; adaptive query domains and
arbitrary observer effects require separately defined profiles. Diagnostic sites
and generated helper names do not define cryptographic occurrence identity.

[Merlin's transcript operations](https://merlin.cool/transcript/ops.html) are a
concrete labeled/framed API, not a theorem for arbitrary native clients.
[Round-by-round soundness research](https://eprint.iacr.org/2019/1261) and the
[duplex-sponge Fiat–Shamir analysis](https://eprint.iacr.org/2025/536) have distinct
models and premises. Select and state the relevant claim before implementing a
concrete construction. A structural checker, hash implementation and security
argument remain separately reviewable results.
