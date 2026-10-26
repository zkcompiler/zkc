# Reusable security

`zkc_security` provides `ZkcSecurity` and `TestsSecurity` over the probability-free
core. Its package closure contains VCVio, PolyFun and CompPoly, with the shared
[pinned baseline](../docs/dependencies.md), and excludes ArkLib and Clean.

`ZkcSecurity.VCVio` preserves full execution distributions, reachable-state
replacement, Sigma composition and Schnorr simulation. `Families` owns generic
Schnorr-family mathematics and quantitative Sumcheck consumers; deterministic
execution and pointwise completeness remain in core. `FiatShamir`, `Commitment`,
`HashChain`, `Stage` and `Endpoint` supply reusable security interfaces and
consumers with explicit experiment and resource assumptions.
`Commitment.Opening` owns the reusable one-opening family used by joint hash-chain
security. Declaration namespaces and theorem names are retained across moves.

`Examples.Subjects` contains the Schnorr, Schnorr AND, Chaum–Pedersen and Okamoto
subjects. They and the maintained probability clients/tests are default targets.
Libraries may not import these leaf subjects. The upstream VCVio module
`VCVio.Schemes.Schnorr.SigmaProtocol` is reusable mathematics from the pinned provider.

From the repository root:

```sh
python3 scripts/develop.py fetch-lean --deps security
python3 scripts/develop.py lean --deps security
python3 common/tests/run.py lean-security
nix build .#security
```

`checks/check_library.py --integration security` checks imports, exact package
closure and nonoverlapping module roots. The independent declaration audit
checks types, proof bodies, stored private/generated declarations and axiom
closures. `ZkcSecurity.Registry` registers generic schemas and endpoints;
optional schemas live in [the ArkLib package](../integrations/arklib/README.md).
These models do not by themselves prove native correspondence or unspecified
cryptographic assumptions. See [architecture](../docs/architecture.md) and
[formal support](../docs/support.md).

The actual plain aggregate table consumer is configured by
[`Examples/TableMembership/Generation.lean`](ZkcSecurity/Examples/TableMembership/Generation.lean).
With current core/security dependencies already checked (including
`Generation.SubjectABI.Command`, `Generation.OriginalEndpoint`,
`Claims.Completeness`, `Claims.CompiledSoundness`, `Endpoint.DomainSafety` and
`Tools.ClaimConstruction`), run from this directory under the prepared Lean
environment:

```sh
python3 checks/check_table_membership.py /tmp/zkc-table-claims
```

The driver fixes `LEAN_NUM_THREADS=2`, uses the supplied `LEAN_PATH`, and writes
only its output directory. It regenerates and compares the ABI/endpoint twice,
then checks the actual subject, method, canonical requests, receipts and
positive/refusal controls. Its `manifest.json` records commands, generated versus
authored source hashes, byte/line counts and results. This is a compiled-ideal
claim, without a native byte correspondence or baseline acceptance.
