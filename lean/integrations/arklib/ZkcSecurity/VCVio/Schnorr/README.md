# Schnorr Fiat–Shamir extraction

`ZkcSecurity.VCVio.Schnorr.FiatShamir` connects a realized constructed PIR verifier
to VCVio's fixed-statement cached-random-oracle experiment. The optional package
uses the VCVio revision recorded in its owning Lake manifest. The connection uses
`FiatShamir.knowledgeVerifyRun`, `knowledgeExtractor_success`, and
`knowledgeExtractor_challenge_bound`; it does not import an unproved security law.

The source verifier must satisfy `Zkc.Protocols.Schnorr.Common.VerifierContract`.
`Zkc.Protocols.Schnorr.Construction.construct` interprets that actual process:
commitment and response are decoded proof inputs, delivery is internal, and the
challenge operation queries `(binding, commitment)`. `Binding` includes source
identity, construction identity, application context, base, and public key.
Equality of typed keys binds every component. It establishes no byte-encoding
injectivity or authenticity of a source digest.

A supplied constructed subject proves `Construction.Realizes actual program service`,
an equality of processes for every binding and proof. This contract contains no
acceptance or security field. `construct_eq` derives the normalized process from
the source contract. `verifierExecution_eq` then derives the entire monadic
execution, including its final-query event and absence of stops. `verify_eq`,
`verificationRun_eq`, and `verificationRun_eq_trace` prove oracle-program and
cached-game equality; `acceptance_eq` is their probability consequence.

## Experiment and extraction

The base, public key, and application/source/construction context are fixed before
the prover runs. A prover has type

```lean
G → Binding Context G →
  OracleComp (unifSpec + (Binding Context G × G →ₒ F)) (G × F)
```

It may use private uniform coins and adaptively query arbitrary bindings and
commitments, including repeated keys and keys outside the final subject. The
adversary and final verifier share one initially empty cache. A cache miss samples
a uniform field challenge; a hit returns the existing answer. Final verification
always queries the proof's key, including when the prover made no queries.

Let `a = acceptance actual prover binding`, and suppose `nmaHashQueryBound` bounds
every execution path by `Q` adversary RO calls. Repeated calls count toward `Q`.
The theorem `extraction` establishes

```text
a * (a / (Q + 1) - 1 / |F|)
  ≤ Pr[extractor prover binding Q returns w with w • base = key].
```

Arithmetic is in `ENNReal`; subtraction is truncated. The extractor is exactly
VCVio's named replay reduction, with the appended verification query. It reuses
zkc's two-response `extract_public_key` theorem. A failed fork takes VCVio's
uniform-witness fallback. `extractor_challenge_bound` bounds fresh replay
challenge requests by `2 * (Q + 1)`, including failed forks. It bounds neither
uniform coins nor runtime. The field/challenge/witness/response type is `F`; the
statement and commitment type is `G`, an additive commutative `F`-module.
Decidable equality, finite uniform sampling, and the stated algebraic structures
are explicit Lean parameters. `generable` is a proved relation generator, not a
hardness assumption.

These are ordinary total `OracleComp` provers. There is no polynomial-time
adversary restriction or efficient-extraction claim. This is a fixed-statement
quantitative extraction result, not an adaptive-statement, signature, concurrent,
multi-session, zero-knowledge, or concrete-provider security theorem. A tiny
finite example proves acceptance one and strictly positive lower bound
`2⁻¹ - 5⁻¹`; it supplies no discrete-log hardness evidence.

`extractionProperty` and `extractionConsumer` use the existing
`Zkc.Verification.Property`/`Consumer` API. The source certificate is a checked
input; the constructed-subject contract is `Realizes`; the property assumption
is the explicit adversary query bound. No security conclusion is supplied by the
caller.

## Actual constructed native profile

`Zkc.Protocols.Schnorr.NativeConstruction` interprets the scalar primitive profile
of an admitted `Zkc.Source.Constructed.Imported`. Group/field algebra uses the
actual operands. Receives supply decoded proof values. Group observation records
the commitment in the returned transcript state; sampling reads that live state
and returns both the challenge and successor state. Field observations retain the
delivered challenge and response. Missing commitment, repeated sampling, wrong
challenge delivery, nonempty dynamic coordinates, repeated response observation,
and unsupported primitive names/type signatures produce a refused stop.

`verifier` preserves the full imported denotation before an explicit final
Boolean projection. Its input/output shape proofs establish only shapes.
`ZkcSecurity.Examples.SchnorrConstructed.full_denotation` normalizes the actual
retained Helpers candidate, including its final transcript; `realizes` proves its
process contract, and `extraction` applies the security theorem.
`source_bound_extraction` selects the source/candidate identities from the
[retained export](../../Examples/fixtures/README.md), with application/base/key
supplied explicitly. Its typed context also retains the exact policy and every
primitive occurrence descriptor. The generated fixture uses the constructed
normalizer's checked raw-erasure admission and full denotation proof. The common-source
example also supports original, Helpers, and reordered certificates through one
consumer.

The selected primitive interpretation is canonical typed RO semantics. The native
candidate still declares `merlin3.bls12-381.fr64be/0`. Metadata and Local bodies are
retained in the imported subject; static framing attributes are not decoded as
bytes by this interpretation. A reviewed request driver must check those exact
descriptors and bind source/candidate/policy identities independently. Native
export authenticity, parsing/rendering, lowering/runtime, proof codecs, native
arithmetic, host initialization, framing injection, hash/sponge behavior, and
sampling conformance remain external boundaries. This module does not prove
Merlin implements the selected oracle experiment.

## Validation

Build from `lean/integrations/arklib`:

```sh
lake build ZkcSecurity.VCVio.Schnorr.FiatShamir
lake build ZkcSecurity.Examples.SchnorrFiatShamir
lake build ZkcSecurity.Examples.SchnorrConstructed
lake env lean TestsSecurity/SchnorrFiatShamirAudit.lean
```

The standalone audit covers all new core, optional, example, and fixture modules,
including private/generated declarations, their types and bodies, and transitive
axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The controls
exercise final-query charging, absent fork points without completion, cache reuse
versus reset, changed binding/commitment, invalid responses, and native state
threading. Aggregate import/audit registration belongs to package integration.
