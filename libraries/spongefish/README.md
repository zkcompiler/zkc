# Spongefish byte transcripts

These ordinary source modules reproduce the SHAKE128 transcript and Schnorr
message order of Spongefish 0.7.4, specialized to arkworks 0.6 BLS12-381 G1.
They use the common compiler, participant Runner and bounded byte transport.

`spongefish` exports initialization, point/scalar observation, scalar challenge
sampling and checked point/scalar reads. Protocol identifiers are padded to
64 bytes within a 168-byte rate block. Session initialization uses the upstream
session tag and 32-byte session digest. Scalars use canonical big-endian bytes;
challenges reduce 64 big-endian XOF bytes. G1 uses 48-byte compressed subgroup
encodings. Decoding succeeds before observation. A final response is observed
even when no later challenge is requested.

`spongefish::schnorr::Schnorr` obtains its nonce from the prover's `Random`
service. `produce` accepts an explicit nonce for composition and deterministic
tests; callers must ensure its secrecy, independence and freshness. `verify`
checks the group equation before EOF. The protocol sends a single `Bytes` value
containing the 48-byte commitment and 32-byte response. It does not add a zkc
artifact identity, session or message prefix.

`spongefish::bls12_381::Provider` adapts these same transitions to programmable
constructions. The [constructed client](../../examples/projects/constructed-schnorr/README.md)
uses it with the generic Schnorr library and the common stream codec. The
application explicitly selects observations, decoding and record sizes; no
protocol-specific compiler or runtime path is involved.

The [explicit transcript reference](../../examples/projects/spongefish-schnorr/README.md) selects
`RawBytes`. Generic signatures do not make the fixed-width record a format for
every group. The current specialization is BLS12-381 G1/Fr. Caller-supplied base,
statement and session values define the statement; applications must authorize
them independently and enforce any additional nonidentity-point requirements.
Interoperability tests establish concrete byte and execution agreement, not
Schnorr security or complete accepted-language equivalence.
