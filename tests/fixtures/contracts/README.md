# Independent contract conformance

`coverage.json` is an authored coverage policy, not a snapshot of signatures or
an installation registry. Every generated operation and type must have exactly
one disposition. A new declaration requires a reviewed disposition and exercised
closed witness; it does not require updating an exact legacy inventory or digest.
The 63 historical atomic pairs form a preservation floor in the test. Additional
installed pairs are tested automatically and do not fail because of their count.

`test_contract_conformance.py` reads the neutral TableGen declaration dump and
the C++ installed nominal catalog as inert data. It enumerates a bounded set of
closed arguments, substitutes them into declaration terms to obtain expected
port spellings, and compares the actual C++, Rust and Lean API observations.
Associated members come from the catalog; no member, capability, signature,
permission, codec or representation table is sent to an independent consumer.
Handwritten signatures and formation/refusal witnesses provide additional checks
that do not derive their expectations from that inventory.

## Driver profile

Each driver reads ASCII JSON lines on stdin and emits one JSON object per line
on stdout, flushing after each response. A final nonempty line without LF also
receives a reply. Input is bounded before JSON parsing: 16,384 bytes per line,
eight JSON container levels and at most sixteen operation arguments. Oversized
lines are drained through LF without retaining their excess bytes. This is a
small test profile, not the full carrier's byte/node boundary test. Duplicate
keys, extra fields, incorrect JSON value kinds and non-ASCII transport refuse.
JSON escapes are supported; decoded spellings still undergo ordinary admission.
An empty line is a refused request. A trailing LF does not create another request.

The three full readers recognize these requests:

```json
{"type":"fixed_vector<field:koala-bear,4>"}
{"physical_type":"fixed_vector<field:koala-bear,4>@plonky3.fixed-vector/1"}
{"contract":"fixed_vector.dot","arguments":["koala-bear","4"],"implementation":"plonky3/fixed_vector.dot","physical":true}
{"facets":"fixed_vector.dot","arguments":["koala-bear","4"]}
```

For an admitted logical type, the exact reply keys are `accepted`, `canonical`,
`copy`, `drop`, `serializable` and `default_physical`. The last value is the full
physical spelling or JSON `null` if no default can be selected. The remaining
values are the canonical logical spelling and Boolean admission/permission
observations. Physical type spellings are not accepted in a logical type request.
For an admitted exact physical type, the reply has exactly `accepted` and
`canonical`, with the full physical spelling in `canonical`.

For an admitted binding, the exact reply keys are `accepted`, `physical`,
`inputs` and `outputs`. Port arrays contain actual resolved spellings, including
outer representation suffixes when `physical` is true. `implementation` is
required and may be the empty string or an exact implementation name. The
empty string is passed unchanged; the driver never silently chooses a provider.

Facet queries first resolve the logical binding with an empty implementation.
Unknown contracts and malformed static arguments therefore refuse before any
classification, including names beginning with `transcript.`. An admitted query
replies with exactly `accepted`, `facets` and `unsupported`. `facets` maps supported
field names to Boolean observations; `unsupported` lists every unsupported
field name. For example, Rust and Lean reply to the example above with:

```json
{"accepted":true,"facets":{"history":false},"unsupported":["publicReplay","sampling","observation","acceptanceGuard","conjunction","unclassifiedProviderEffect"]}
```

The test compares the unsupported names as a set while rejecting duplicates.
`facet-policy.json` records the exact comparison scope:

| Field | C++ | Rust | Lean |
| --- | --- | --- | --- |
| `history` | supported | supported | supported |
| `publicReplay` | supported | unsupported | unsupported |
| `sampling` | supported | unsupported | unsupported |
| `observation` | supported | unsupported | unsupported |
| `acceptanceGuard` | supported | unsupported | unsupported |
| `conjunction` | supported | unsupported | unsupported |
| `unclassifiedProviderEffect` | supported | unsupported | unsupported |

Every declared operation gets an admitted facet witness in each consumer.
Supported flags are compared with inert declaration expectations. Only `history`
has an equivalent actual classifier in all three consumers. Rust's classifier is
crate-private, so its test example compiles the unchanged owning `model.rs`
module through a source-path adapter and calls `observes_or_samples_history`.
It still admits bindings through the linked public runtime API. Lean calls
`Bindings.historyContract`; C++ calls its operation-contract facet APIs. The
example contains no copied classification table and adds no production API.

The other six flags provide C++ declaration-to-API evidence only. Runtime
attribute rules and numerical reference implementations are not substituted
for absent classification APIs. Boolean sampler and observation presence does
not check their port-role payloads. Diagonal, contraction, coset and domain-value
facts have explicit uncompared dispositions. A new facet kind fails until its
disposition is reviewed. The provider-effect flag uses input-head custody for
the expected result only after verifying that declarations have no open or
affine nested Type terms. Cases outside that subset explicitly require a
coverage review. The actual C++ API also propagates uncertainty through Type
arguments; this test does not claim a full instantiated affine-effect analysis.

Every rejected request emits exactly `{"accepted":false}`. Diagnostic prose is
not a cross-consumer contract. Drivers continue after a refusal. Failures of the
process itself, missing tools, invalid replies or missing reply lines fail the
harness rather than counting as admission refusals.

The C++ driver calls `parseBoundType`, `defaultRepresentation` and
`resolveBinding`; the Rust driver calls `LogicalType::parse`, fallible
`PhysicalType::{parse,default_for}`, and `OperationBinding::{logical_signature,signature}`;
the Lean driver calls `Bindings.valueType`, checked default selection,
`Logical.permissions` and `Bindings.resolve`. Each uses its owner's permission
APIs. No driver reproduces an operation signature or implements its arithmetic.

## Independent physical registry discovery

`{"implementations":true}` queries each reader's installed `(contract,
implementation)` identities. C++ exports its physical catalog; Rust runtime,
Lean and the executing Rust backend each enumerate their own explicit registry.
The response contains `accepted`, `discovery` (`physical-registry`) and an
`implementations` array of objects with `contract` and `implementation` keys.
The harness probes the union: none of these registries is populated from another
reader's answer. Lean no longer scans expression literals to guess names.

The `backend_contract_conformance` example supports discovery and physical
binding requests only. Its signature observations call `NativeBackend`'s actual
binding resolver. These form a fourth physical reader; logical formation and
semantic facets remain a three-reader comparison. Backend negative requests,
option refusal and bounded transport are tested too.

Every explicit alternative needs an accepted closed witness in every reader.
Rust and Lean default provider/contract registrations can be inactive where
nominal applicability narrows them; the reports identify those rows explicitly.
C++'s `resource_unit.*` and `table.relayout` paths currently resolve outside its
catalog: their identities are supplied by the independently discovered union,
and their signatures still participate. Signature agreement is separate from
the backend tests that execute every alternative and compare its result with
the original implementation.

## Representation observations

The catalog observer exports every atomic representation with its complete
kind/domain/representation key, default flag and layout. The harness checks
exact physical admission and default selection through all three consumers,
including other installed representations of the same kind and an unknown name.
Logical formation does not require a default representation.

The C++ catalog observer exports `applied_representations` from the actual
`appliedTypeRepresentations()` API. Each row has `constructor`, `arguments`,
`representation` and Boolean `default`. Argument patterns are exactly
`{"kind":"Type","exact":"..."}`, `{"kind":"Domain","exact":"..."}` or
`{"kind":"Nat","minimum":0,"maximum":N}`. Nat ranges are inclusive; the API's
implicit lower bound is exported explicitly. Type patterns contain complete
logical spellings, not just constructor heads.

The harness generates positive, default-selection and exact-physical queries
from every row. Nat probes use both endpoints and their neighbors. Type and
Domain probes vary one argument at a time over relevant installed atomic types
or nominals and an unknown spelling. Tests try all same-constructor installed
representation names plus an unknown representation. There are at most 256
logical probes and 1,024 requests; there is no Cartesian product of ranges and
no vector allocation or numerical execution proportional to a Nat argument.

The generated pattern match supplies inert expectations only. Each consumer's
ordinary type API decides logical and exact physical admission. Every pattern
must have positive admission, and the tests preserve per-pattern witness lists.
Out-of-pattern spellings may be logically invalid or valid without a physical
representation; those observations must agree across consumers. Representation
identity describes an ABI, not exclusive ownership by an implementation provider.
Independent logical operation witnesses remain in place alongside these
generated physical checks.

## Dispositions and limits

The operation groups choose closed arguments: field/group/commitment/transcript
nominals; a fixed-vector Field/Nat witness; finite transcript/codec pairs; core
nullary operations; and the separately formed `resource_unit:Ticket`. The latter
has no generic scope carrying its nominal slot, so its substitution is explicit.
Each operation must have at least one accepted closed case in each consumer.
Unsupported instances are still compared; refusals are not silently skipped.
The number of candidates has an explicit ceiling to require review of growth.

`scalar` and `capability` are declared types outside this common-carrier
formation profile and receive explicit refusal probes. Fixed vectors over BLS,
nested fixed vectors and resource elements are logically admitted, with physical
unavailability tested separately. Conditional copy/drop applies even to zero
length. Fixed vectors have no installed public codec or observation operation.
A BLS fixed-vector signature can be admitted without a physical implementation;
this does not claim a BLS reference execution or backend.

This suite compares admission, the signatures consumed by interpretation and
the semantic classifications described above.
It does not invoke cryptographic kernels, prove interpretation equality, replace
mapping/facet tests, authorize source imports or establish a security theorem.
Native and Lean numerical interpretation tests and full protocol integration
remain separate. The retired legacy comparison is historical migration evidence,
not the current conformance oracle.

The cross-build test uses ordinary `Toolchain` lookup and fails if a required
executable is missing. Main owns CMake and Lake registrations. With the compiler and Lean tools and both Rust conformance examples built, run:

```sh
uv run --no-sync --locked pytest tests/protocol/test_contract_conformance.py
```

Per-test reports preserve request/reply lines, complete disagreements and
per-operation accepted counts. There are no expected-failure exemptions for
consumer disagreement.
