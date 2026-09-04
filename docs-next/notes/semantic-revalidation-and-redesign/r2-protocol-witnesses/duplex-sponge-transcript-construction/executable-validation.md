# Executable Validation

> **Kind:** Temporary finite-evidence record
> **State:** Complete at the frozen finite evidence boundary
> **Authority:** None. The retained evaluator is a falsifier for the named
> finite construction. It is not a semantic implementation, cryptographic
> primitive, theorem proof, or production endpoint.

## 1. Question and result

The executable package asks whether independently written finite transition
relations can agree on the source-sensitive duplex edges while rejecting the
specific alternatives that motivated a distinct construction family.

The answer is affirmative at the frozen finite scope. The evaluator reproduces
one three-round verifier trace, distinguishes the prover-required prefix from
the verifier-complete schedule, preserves one Core across Fresh and duplex
Protocol identities, and kills the selected transition and admission
mutations. A separate negative result records that none of this establishes a
security theorem.

The retained package is
[`evaluation/duplex-sponge-transcript/`](../../../../../evaluation/duplex-sponge-transcript/README.md).

## 2. Frozen subject

```text
alphabet       = {0,1,2,3,4}
rate           = 3
capacity       = 2
instance       = 0x0409
salt           = (2,4)
messages       = ((3,1), Unit, (1,2,3))
message lengths= (2,0,3)
squeeze lengths= (2,1,4)
```

The provider is one small deterministic hash-to-capacity function and one
affine permutation over all `5^5` states. Exhaustive bijection checking is a
finite fixture fact only. It gives no random-function, ideal-permutation,
sponge, entropy, collision-resistance, or concrete-security evidence.

The public verifier derives:

```text
challenges        = ((1,0), 2, (4,2,2,2))
permutation calls = 5
trace events      = 8
```

The owner-side support-point replay derives only the first two challenges. It
does not execute the final squeeze after the last prover message. The verifier
does. The sidecar supplies declassified material for this check; it is not an
adaptive prover-strategy execution and proves no generation necessity.

## 3. Independent relation and discriminators

The primary transition implementation and a separately coded literal relation
agree exhaustively on the bounded absorb and squeeze domains. The retained
edge witnesses cover:

- initialization from the runtime instance;
- empty absorption resetting only the squeeze cursor;
- lazy permutation at an exact rate boundary;
- overwrite rather than combination or XOR;
- zero-length squeeze as complete state identity;
- continuation across adjacent squeezes;
- absorption after a partial squeeze;
- raw fixed-codec message absorption;
- salt before every prover message;
- no decoded-challenge reabsorption; and
- the final verifier-only transition.

The mutation suite distinguishes wrong state laws and wrong construction
shapes, including eager boundary permutation, empty-absorb identity,
output-stream restart, prefix-XOF substitution, misplaced salt, challenge
reabsorption, omitted or reordered message/challenge maps, partial decoders,
noninjective or variable-length encoders, and construction/Core substitution.

This mutation set is selected, not complete. Passing it says that the frozen
trace is not compatible with those named alternatives; it does not establish
generality.

## 4. Identity and authority pressure

The finite model keeps four different lanes:

| Lane | Contents |
|---|---|
| Semantic subject | Closed Core, construction, exact execution-defining algorithm/codec coordinates, and Fresh/duplex Protocol roots |
| Runtime invocation | Statement, proof-carried salt, messages, and replay limits |
| Validation basis | Source and evaluator bytes used to reproduce the report |
| Owner support point | Declassified material used only for the owner-prefix check |

Runtime values do not rotate construction identity. Changing an exact
execution-defining semantic coordinate does. The proof tuple itself need not
serialize a construction ID, but replay is bound to the authenticated expected
construction and Protocol context. Public replay does not read the private
support point.

The source ledger is inert validation metadata. Its bytes can rotate the
validation basis but never the semantic Core, construction, or Protocol roots.
It is not source authentication or theorem authority.

## 5. Reproduction contract

From the repository root:

```sh
python3 -B -m unittest discover \
  -s evaluation/duplex-sponge-transcript/tests -v
python3 -B evaluation/duplex-sponge-transcript/run.py --check
python3 -B evaluation/duplex-sponge-transcript/generate.py --check-fixtures
```

The first command runs transition, construction, execution, identity,
provenance, mutation, and report tests. The second builds the public report
before opening the frozen expected projection. The third checks the owner
support point without writing the checkout.

The final closure run and exact test count are recorded in
[Convergence and Promotion](convergence-and-promotion.md), rather than copied
into several temporary pages.

## 6. Exact evidence boundary

An affirmative executable result establishes only:

- agreement of the two finite transition implementations;
- reproduction of the frozen public trace and exact resource counts;
- rejection of the named finite mutations;
- separation of runtime, semantic, validation, and private-support inputs; and
- same-Core/distinct-Protocol identity within this finite model.

It establishes none of:

- soundness, knowledge soundness, completeness, zero knowledge, RBR, ROM,
  QROM, UC, multi-instance, or composition security;
- ideality or security of the fixture hash or permutation;
- uniformity, independence, or freshness of the supplied salt;
- correctness of the reviewed paper's reductions;
- conformance of the production compiler or runtime;
- proof-byte parsing, endpoint safety, constant-time behavior, or a production
  ciphersuite; or
- support for arbitrary duplex constructions or public-coin protocols.

The residual trust is the Python runtime, filesystem stability during one
replay, correctness of both finite implementations, and the manual source
reconstruction. Agreement between independently written functions reduces one
implementation risk; it is not a formal proof.
