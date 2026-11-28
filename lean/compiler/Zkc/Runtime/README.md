# Runtime (`Zkc.Runtime`)

Concrete cryptographic runtime and execution engine for deployed Core schemes, packaged as the
`ZkcRuntime` library of `zkc_compiler` (`lean/compiler`). It sits outside the audited default
targets (`ZkcCore`, `ZkcVocabulary`, `ZkcSubject`), imports `Zkc.Core` and `Zkc.Vocabulary`, and
is verified end-to-end by `just test-runtime`.

## Modules

| Module | Holds |
|---|---|
| `Crypto/Fields.lean` | Prime-field arithmetic for KoalaBear (`p = 2^31 - 2^24 + 1`), BLS12-381 `Fr` and `Fq`, quartic extension `KoalaBear4 = F_p[x] / (x^4 - 3)`, 2-adic roots of unity, and fixed-width LE/BE byte conversions |
| `Crypto/Curve.lean` | BLS12-381 `G1` affine and Jacobian projective arithmetic, prime-order subgroup checks (`g1InGroup`), and canonical 48-byte ZCash compression/decompression (`compressG1`, `decompressG1`) |
| `Crypto/Hash.lean` | FIPS 180-4 SHA-256, Keccak-256, FIPS 202 SHAKE128 / SHAKE256, TurboSHAKE128 (12-round Keccak), and Poseidon2 over KoalaBear (width 16, rate 8, S-box `x^3`) |
| `Crypto/Suites.lean` | Concrete Fiat–Shamir transcripts: Merlin 1.0 (STROBEv1.0.2), CFRG `draft-irtf-cfrg-fiat-shamir-04` Duplex (SHAKE128 & TurboSHAKE128), Poseidon2-KoalaBear duplex, and deterministic Schnorr signature helpers |
| `Model.lean` | Verified `standardModel : Core.Model Zkc.Vocabulary.standard` and `linkedModel? (b : Project.Bindings) : Except String (Core.Model b.vocabulary)` proving `defined`, `total`, `decides`, `keeps`, `literals`, and `supported` for every standard and project-bound runtime row |
| `Codecs.lean` | Canonical byte formats (`formatKoalaBear`, `formatBls12381Fr`, `formatKoalaBear4` with `Format.Lawful` proofs), `HList` canonical codecs, and hex conversion helpers (`bytesToHex`, `hexToBytes`) |
| `Source.lean` | Deterministic `Core.Source` providers: `emptySource` (zero randomness for deterministic nonce/Fiat–Shamir schemes) and `seededSource` (SHAKE128 PRNG keyed by `(seed, occurrence)`) |
| `Execute.lean` | Unified execution drivers: `runDeployed` (`Core.execute`), `runClosed` / `runDeployedClosed` (direct executor over specialized `Core.ClosedRole` + `ClosedProcs` without intermediate handler stacks), and `runInteractiveScheme` (`Core.runInteractive`) |
| `CfrgVectors.lean` | Byte-exact verification of Appendices C.2, C.3, C.5.1, and C.5.2 of `draft-irtf-cfrg-fiat-shamir-04` for both SHAKE128 and TurboSHAKE128, both directly over `Cfrg.Duplex` and end-to-end through `Core.admit`, `Core.deploy`, `Core.execute`, and `Core.specialize` + `runClosed` |

## Verification

Run `just test-runtime` from the repository root (or `lake exe zkc-runtime-tests` and
`lake exe zkc-check cfrg-vectors` from `lean/compiler`). The test suite (`Zkc/Tests/Runtime/`)
checks:

- Finite-field, BLS12-381 `G1`, hash/XOF/Poseidon2, and canonical codec unit invariants and
  negative controls (`Crypto.lean`).
- All 33 CFRG `draft-irtf-cfrg-fiat-shamir-04` vectors across SHAKE128 and TurboSHAKE128.
- End-to-end differential `Core.execute == runClosed` verification across real `.zkc` examples
  (`schnorr_example.zkc` `Proof` & compact deterministic `Signature`, `chaum_pedersen.zkc` pure
  Core IR `HashChain<Keccak256, Fr>`, `sigma_or.zkc`, 10-round `sumcheck_example.zkc`, native
  `Poseidon2KoalaBear`, `interactive` Schnorr, bounded `retry` with rollback and exhaustion, and
  `deployProtocolWithSuite` with `HashChain<Sha256, Fr>` and CFRG SHAKE128) (`Examples.lean`).
