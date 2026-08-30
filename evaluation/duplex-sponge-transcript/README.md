# Duplex-Sponge Transcript Construction Evaluator

This package is a finite executable falsifier for one source-shaped
`DuplexSpongeTranscriptConstruction`. It checks the reviewed transition edges,
closed codec and occurrence maps, proof-carried salt lifecycle, a bounded
generation-prefix simulation, construction identity, and public replay.

It is independent of the target documentation and earlier reference models.
It is an evaluation instrument, not semantic authority, a compiler component,
a production transcript implementation, or cryptographic evidence.

## Run

From the repository root:

```sh
python3 -B -m unittest discover \
  -s evaluation/duplex-sponge-transcript/tests -v
python3 -B evaluation/duplex-sponge-transcript/run.py --check
python3 -B evaluation/duplex-sponge-transcript/generate.py --check-fixtures
```

The first command exercises the source transition, an independently coded
literal relation, structural construction admission, finite source
applicability, mutations, identity boundaries, public provenance, generation
support separation, and copied-checkout replay. Plain `run.py` builds and emits
without consulting the frozen projection; `--check` additionally performs a
strict rebuild before opening and comparing that projection. `generate.py`
reads the declassified private sidecar, reconstructs the frozen proof bytes,
and simulates the selected first-two-challenge prefix. It does not implement a
prover, establish challenge necessity, infer entropy quality, or write files.

## Frozen finite profile

The alphabet is `Sigma5 = {0,1,2,3,4}` with rate three and capacity two.
`Sigma5` has no protocol-field semantics. The runtime instance bytes are
`04 09`, the salt is `(2,4)`, and the three prover-message codecs are:

| Round | Message type | Codec | Challenge squeeze and decoder |
|---:|---|---|---|
| 1 | `SigmaPair` | identity, length 2 | length 2, pair identity |
| 2 | `Unit` | empty, length 0 | length 1, scalar identity |
| 3 | `SigmaTriple` | identity, length 3 | length 4, quadruple identity |

The deterministic transition provider is:

```text
h(x) = (sum_i x_i mod 5, sum_i (i+1)x_i mod 5)

p(a,b,c,d,e) = (
  a+b+1,
  b+c+2,
  c+d+3,
  d+e+4,
  e+a
) mod 5
```

The construction identity contains the exact affine matrices and offsets for
`h` and `p`, rather than only their provider-interface names. The finite
source-applicability check enumerates all `5^5` provider states; a baseline-only
test also checks the separately written inverse. This establishes only the
closed fixture's bijectivity. The provider is deterministic, small,
algebraically transparent, and unsuitable for cryptography by design.

The public proof contains:

```text
salt = (2,4)
messages = ((3,1), Unit, (1,2,3))
```

Public verification derives challenges `((1,0), 2, (4,2,2,2))` and makes five
permutation calls. The generation-support check simulates only `((1,0), 2)` by
an explicit fixture policy; that omission is not a claim about what every
prover needs.

## Two distinct judgments

Structural construction admission checks the closed term shape, typed root
Statement binding, exact and ordered occurrence maps, fixed-length total
message encoders, instance projection, and declared algorithms. It does not
claim that a generic PIR construction has injective encoders or a bijective
provider.

The separate finite source-applicability check establishes, only by exhaustive
enumeration of this closed carrier, that the declared provider is bijective,
the message encoders are injective, and the challenge decoders are total and
well typed. Noninjective encoders and nonbijective affine providers remain
structurally representable and fail this second check instead.

## Transition boundary

The primary and independent models both implement these source-sensitive
rules:

- `Start_h(x)` forms `((0^rate,h(x)),0,rate)`;
- every Absorb call sets the squeeze index to the rate, including empty input;
- absorption applies the permutation only before processing another symbol
  when the absorb index is already full;
- absorption overwrites rather than XORs the selected rate cell;
- `Squeeze(0)` is the exact state identity;
- a positive squeeze resets the absorb index, permutes only when the squeeze
  index is full, and continues an existing partial output stream; and
- adjacent positive squeezes without an intervening absorb equal one
  concatenated squeeze.

The mutations distinguish empty-absorb no-op, eager permutation, combining
instead of overwriting, output-stream restart, reset-to-zero after an
absorb-side permutation, prefix-XOF substitution, salt after the first message,
decoded-challenge reabsorption, omission of the final verifier squeeze,
serialized verifier challenges, incomplete or reordered occurrence maps,
noninjective or variable-length prover codecs, partial decoders, wrong decoder
result types, and construction/Core identity substitution. A kind-incompatible
positional message substitution is malformed; reordering same-typed values
would simply produce different proof contents.

A total biased challenge decoder is not malformed. The finite model computes
its exact statistical distance and rotates construction identity; theorem
applicability remains a separate question.

## Fixture and authority boundaries

| Path | Role |
|---|---|
| `cases/construction.json` | Public closed Core view and construction declaration. |
| `cases/public-inputs.json` | Runtime Statement and replay-only resource limits. |
| `cases/public-proof.json` | Proof-carried salt and prover messages; verifier challenges are absent. |
| `cases/source-ledger.json` | Exact inert source metadata anchors and declared digests; no pinned source bytes, source authentication, or theorem authority. |
| `cases/expected-results.json` | Regression projection opened only after report construction and strict verification. |
| `cases/private-generation.json` | Declassified generation-support point used by `generate.py` and its tests; excluded from public replay and every public identity or digest. |
| `duplexmodel/transition.py` | Primary literal transition implementation and validation-only provider. |
| `duplexmodel/independent.py` | Separately coded transition relation. |
| `duplexmodel/construction.py` | Closed construction, codec, decoder, identity, and admission checks. |
| `duplexmodel/execution.py` | Prepared public replay and bounded generation-prefix simulation. |
| `duplexmodel/provenance.py` | Fixture, loaded-root, source-manifest, and validation-basis binding. |
| `duplexmodel/report.py` | Deterministic public report and post-build expected projection. |

Construction identity includes the Core identity and typed root Statement
binding, construction kind, alphabet/rate/capacity, exact ordered instance
projection, salt length, transition laws, provider interface, affine provider
algorithm and parameters, and exact ordered codec/decoder algorithms. A
prepared replay separately binds the derived Core, construction, duplex
Protocol, and typed Statement invocation; none of those IDs is serialized into
proof bytes. Runtime instance, salt, messages, validator source bytes, replay
limits, and source-ledger bytes do not silently become construction meaning.
They instead affect the appropriate invocation, proof, validation-basis,
evidence, or report lanes.

Fresh and duplex-sponge Protocols refer to one exact Core and have distinct
Protocol identities. This package does not implement the existing
canonical-framed construction; that construction's own executable gate must be
rerun when this candidate is integrated. All IDs here use the evaluator's
fixture-local semantic regime; they are candidates, not assertions that the
durable PIR regime has already assigned these exact identifiers.

## Nonclaims and residual trust

The package does not establish:

- that the deterministic `h` is a random function;
- that the finite affine bijection is an ideal random permutation, a secure
  permutation, an indifferentiable sponge, or a concrete ciphersuite;
- uniform or independent salt generation;
- Fiat--Shamir soundness, knowledge soundness, completeness, or zero knowledge;
- state-restoration security or an adversary experiment with inverse access;
- ROM, QROM, or UC security;
- codec adequacy outside the exhaustively finite profile;
- production endpoint parsing or serialization;
- durable PIR ABI conformance, compiler correctness, or implementation
  support; or
- general support for duplex constructions or public-coin protocols.

The evidence trusts the Python interpreter and runtime, stable source and
fixture bytes during one replay, filesystem behavior, the manual source
reconstruction, and correctness of both finite implementations. Exact
agreement between them is implementation-diversity evidence, not an
independent formal proof.
