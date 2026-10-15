# Structured native import

The [native export contract](../../../docs/spec/formats/structured-source.md)
owns `zkc.structured-source/0`. This page owns its independent Lean admission and
logical meaning. It complements the scalar importer; neither silently changes
the other's vocabulary or scope.

## Checked subject

`Zkc.Source.Structured.Snapshot` retains source identity, selected entry and
participant, every domain and definition, visibility, origins, preconditions,
sites, operand positions and ordered results. `Format` reads exact tagged arrays
and rejects unknown tags, extra fields, JSON objects, noncanonical numeric tokens
and unsupported vocabulary, including in dormant bodies.
Logical-origin binding values remain opaque retained metadata. Their membership
in the native identity language is checked by the native verifier; Lean checks
the pair structure, lengths, nonemptiness and key uniqueness.

`check` independently resolves types, helper kinds and signatures, exact bound
provenance, capture forwarding and acyclic dependencies. Each function body is
lowered to the shared `RawRegion` and formed by `RawRegion.elaborate`. A finite
declaration lowers to an owned fold using its exact declaration ABI. Each checked
body is stored once; calls retain named references instead of expanding syntax.

`Imported snapshot` uses the common `Verification.Imported` carrier. Its check
witness ties the resulting program to that exact snapshot.
`CheckedDefinition.exactBody` proves that erasure recovers the lowered raw body;
`Imported.exactSubject` retains the complete source descriptor. These are
formation and subject-binding facts. A successful computational bounds check
does not itself constitute a general theorem that every admitted Math function
is total.

## Static bounds

A bound records an exact index/container pair. Result binding shifts both
positions. Conservative result-to-input summaries follow direct returns,
reordered or repeated outputs, shared Math calls and identical select arms.
Each Math helper is summarized once after its callees, without expanding calls.
Admission normalizes operand identities through these summaries; unknown results
receive fresh identities. The summary algorithm is a computational check;
its general semantic preservation theorem remains a separate obligation.
Local control regions start without facts because Local definitions
cannot declare bound premises in this profile.
Math preconditions are local assumptions, instantiated and discharged at every
call. An indices domain supplies the bound for its selected vector in the
step's `S / I / A / C` interface, including another invariant formal supplied
with the exact same SSA value. Mutable state is not assumed invariant across
iterations. Matching types or equal lengths do not identify vector contents.

Math cannot contain an authored stop or invoke Local code. Local code may stop, including during
a zero-result call. The profile admits only immutable Boolean, index, scalar
and vector values. It makes no affine ownership claim.

## Owned meaning

`Meaning` assigns the nominal field explicitly to a commutative ring `F`,
indices to natural numbers and vectors to lists. The command-line runner uses
the actual BLS12-381 scalar modulus:

```text
52435875175126190479447740508185965837690552500527637822603658699938581184513
```

The meaning is a closed `PIR.Proc`, preserving returned ordered values and all
stop reasons. Named helpers resolve through an acyclic table of already
interpreted checked bodies; semantics has no arbitrary recursion fuel. Region
callbacks are invoked with closed arguments. The owned operations do not
inspect callback process constructors.

The defensive helper-resolution fallback and failed checked reads both stop
with `refused`, as does an authored `refused` stop. General theorems ruling out
the internal cases for admitted valid inputs remain separate obligations.
Successful admission is a computational check, not a proof of native formation,
general read safety or Math totality. `check_ok_inversion` states only successful
checking and exact subject retention.

Folds use the shared ordered `Finite.execute`: domain admission precedes
iteration, the predicate precedes each selected step, false preserves current
state, and a stop bypasses the suffix. `boundedAt` is a checked read; an invalid
index refuses rather than returning an arbitrary default. Counted loops retain
their state/capture split and conditional completion flag.

## Tools and practical bounds

```text
structured-source check SNAPSHOT.json
structured-source run SNAPSHOT.json INPUTS.json
```

Inputs are an ordered array of typed values:

```text
["bool", value]
["index", unsigned-number]
["field", "bls12-381.fr", canonical-decimal-string]
["vector", "bls12-381.fr", [canonical-decimal-strings...]]
```

A run returns `["returned", typed-values]` or `["stopped", reason]`.
Import, input and evaluation-capacity refusals have a nonzero tool exit; they
are distinct from successfully reporting a semantic stop.

Admission bounds snapshot bytes to 1 MiB, strings to 512 bytes, domains and
definitions to 128 each, signatures to 512, instructions and references to
4096, nesting and helper depth to 64, and stored dependency edges to 100000.
Shared call trees are not expanded during admission. The separate CLI work
estimate can refuse an admitted helper DAG whose execution would be too large.
The CLI has additional input and evaluation limits so a valid mathematical
program need not be executed with unbounded host resources. These limits do
not become fuel parameters in semantic theorems.

## Verification scope

The first clients concern the actual total-state and unit-state finite native
fixtures. Their complete model equations distinguish ordered multiple results
and stopping zero-result folds. Schnorr and quadratic Sumcheck are the subsequent
whole-protocol targets described in the
[design](../design/structured-native-import.md); the current single-participant
profile does not import their group/service communication.

Native parsing/formation, C++ export, JSON parsing and transparent constructor
rendering remain reviewed executable boundaries. The byte digest identifies
a subject and cannot replace correspondence. Model equations and bounded
native comparisons establish different claims. Frontend and optimizer
correctness, participant projection, native cleanup/capacity, production
arithmetic/sampling and cryptographic security require separate connections.
