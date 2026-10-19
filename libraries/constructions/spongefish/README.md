# Spongefish byte transcripts

These ordinary source modules reproduce the SHAKE128 transcript and Schnorr
message order of Spongefish 0.7.4, specialized to arkworks 0.6 BLS12-381 G1.
They use the common compiler, participant Runner and bounded byte transport.

`spongefish::duplex` owns byte initialization, absorption and squeezing.
`spongefish::bls12_381` owns concrete G1/Fr observation, scalar challenge
sampling and checked 48/32-byte point/scalar reads. `observe_scalars` leaves the same state
and produces the same later challenges as successive scalar observations. An
empty vector leaves the state unchanged, even after a challenge. This helper
defines scalar-loop equivalence; it does not claim equivalence with an upstream
slice-observation API. It adds no length framing, so callers must bind vector
lengths through the statement or earlier observations.

Bulk observation allocates a contiguous `32*n`-byte encoding and temporary
storage of the same size, subject to the byte and output limits. It can therefore
refuse a vector that scalar observations process separately; it also charges
less SHAKE work than those separate calls. Protocol identifiers are padded to
64 bytes within a 168-byte rate block. Session initialization uses the upstream
session tag and 32-byte session digest. Scalars use canonical big-endian bytes;
challenges reduce 64 big-endian XOF bytes. G1 uses 48-byte compressed subgroup
encodings. Decoding succeeds before observation. A final response is observed
even when no later challenge is requested.

`spongefish::bls12_381::schnorr::Schnorr` obtains its nonce from the prover's `Random`
service. `produce` accepts an explicit nonce for composition and deterministic
tests; callers must ensure its secrecy, independence and freshness. `verify`
checks the group equation before EOF. The protocol sends a single `Bytes` value
containing the 48-byte commitment and 32-byte response. It does not add a zkc
artifact identity, session or message prefix.

`spongefish::bls12_381::Provider` adapts these same transitions to programmable
constructions. The [constructed client](../../../examples/projects/schnorr/spongefish/README.md)
uses it with the generic Schnorr library and the common stream codec. The
application explicitly selects observations, decoding and record sizes; no
protocol-specific compiler or runtime path is involved.

The [explicit transcript reference](../../../common/tests/fixtures/projects/spongefish-schnorr/README.md) selects
`RawBytes`. Typed signatures select BLS12-381 G1/Fr and refuse other groups. Caller-supplied base,
statement and session values define the statement; applications must authorize
them independently and enforce any additional nonidentity-point requirements.
Interoperability tests establish concrete byte and execution agreement, not
Schnorr security or complete accepted-language equivalence.
