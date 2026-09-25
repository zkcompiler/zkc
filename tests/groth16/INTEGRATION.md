# Relation-aware zkc integration evidence

After the integration worker delivered the actual R1CS-aware CLI,
[`run_zkc.py`](run_zkc.py) executed both preserved fixtures through the separately
built compiler, Lean checker and Rust tool. The [compact receipt](evidence/zkc-integration.json)
records executable/PIR hashes, native relation identities, emitted source and
endpoint hashes, fixed-proof hashes, timings, and every observed outcome.
This is evidence for these two fixtures with a public, insecure test setup.
The original 80 fixture controls remain separately recorded in [REPORT.md](REPORT.md).
The CLI receipt was refreshed after the code-review repairs; its executable
hashes, timing observations and identity-basis fields describe that final run.
Only its own checksum changed in `SHA256SUMS`. The original relation/key/proof
fixtures, 80 controls and deterministic algebra manifests were preserved.

The four fixed `(r,s)=(1,2)` / `(0,0)` zkc proofs equal the controlled upstream
proofs at every canonical field and point coordinate. Both fixed bound artifacts
repeat exactly. At each depth, two OS-randomized zkc proofs differ and verify in
the untouched snarkjs CLI, and a fresh unmodified upstream proof verifies through
the zkc endpoint. Fixed upstream proofs also verify through zkc.

The initial prover invocation takes the complete authored PIR and actual binary
R1CS through the delivered relation-resolution/materialization, compilation and
Lean admission route. Later verifier invocations use the saved common source,
physical endpoints and expected relation identity, plus only the verification
key, public statement, application context and candidate proof. They receive no
R1CS, proving key or witness.

On that cached path, the relation identity is application-declared context,
matched to the saved source's origin labels. It is re-derived from relation
contents only on the `--source`/`--r1cs` path. The cache and intended verification
key must be authenticated by the application; origin labels and transport
binding do not prove relation-to-key correspondence. The CLI records this
distinction in `relation_identity_basis`.

Eight additional negative cases at each depth passed, for **16 zkc refusal
controls**: changed root, noncanonical root, negated A, swapped G2 coefficients,
wrong framed-artifact context, wrong verification key, truncated framing and
altered private witness. The altered private witness is refused before a proof
file is written. These counts are separate from the 80 original controls.

The measured native relation identities are:

- Depth 2: `16dad9fcff1f27effa9aeb61fadc4c3093b7045d8e3eb68736a51f28e2a287cd`.
- Depth 16: `9d7fb92bea1f64ace61571e78c54bd62083f7f4b5635bbd73e6973e17b844945`.

The tool reports the computed field, relation sizes and QAP domain, and
cross-checks the complete imported zkey A/B coefficients, including the added
constant/public rows, against the normalized R1CS. Its binding record explicitly
retains these **external unverified premises**: C/IC/H key derivation, group-query
and setup consistency, and the ceremony. The independent fixture algebra checks
are separately scoped to the selected witnesses and public test trapdoors.

Native relation materialization is an explicit compiler lowering. The Lean
checker admits the resulting ordinary source/endpoints; this run does not add
a proof of elaboration adequacy. Bare snarkjs JSON has no external application
context field; its adapter binds the caller-selected context while checking the
cryptographic equation. Context mismatch rejection here is tested on the bound
internal artifact. Authentic relation selection, key derivation and secure setup
remain application premises.

The runner records process wall time, preparation/admission, key import,
statement binding and three repeated prepared prove/verify executions separately.
These are a small machine-specific sample; no comparative performance or general
conformance claim is inferred. External binary hashes identify this observed
run and are not cross-machine build reproducibility requirements.
