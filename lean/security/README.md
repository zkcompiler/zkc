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
`Examples.Schnorr.SigmaProtocol` is reusable mathematics from the pinned provider.

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
