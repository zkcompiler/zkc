# K3-E bounded cross-consumer coherence witness

This package is a bounded integration checkpoint for the K3 semantic-kernel
co-design pass. It loads the existing K3-C Analysis and K3-D OIR-projection
instruments side by side without adding a third semantics implementation.
Loading K3-C first installs the canonical K3-B, K2, and K1 module objects;
K3-D must reuse those exact objects and source files.

The two consumer branches start independently from the same P01-derived,
total-uniform N=8 `total_uniform_schnorr_case`. This is not the retained
`r2-p01-schnorr` artifact:

- K3-C derives its relation source, checked Fresh/Fiat--Shamir source pair, and
  a finite Schnorr source/experiment profile descriptor. The descriptor selects
  exact coordinates and does not prove special soundness.
- K3-D derives verifier and Plan-bound prover endpoint source views, separately
  constructs and locally admits OIR endpoints, and checks K3-D
  endpoint-source-relative projection propositions by exact graph equality.

There is deliberately no K3-C-to-K3-D capability edge. No Analysis source,
profile, judgment, or capability is consumed by OIR projection. The only
cross-consumer correspondence is `SharedOwnerAnchors`, an inert tuple of typed
IDs derived from the common owner case. K3-E checks the Analysis records and
the two K3-D lanes independently against those IDs. The tuple is a union of
owner coordinates, not a claim that every field is consumed by both branches,
and the shared IDs convey no authority.

The joined gate now traverses both endpoint object graphs and requires them to
contain no Analysis named-premise body, Analysis-local source handle, judgment,
or capability, and no premise identity from the independently formed Analysis
goal. A separate mutation swaps one Analysis premise ID, observes refusal on
the Analysis side, and confirms that both already formed OIR endpoint and
projection-proposition identities remain unchanged.

K3-D's rich endpoint facts that are not yet present in the current K2/K3-B
reference carriers remain an explicit future-owner supplement. K3-D checks the
supplement against live owner-issued K2 static views, one affirmative
`CheckedFSConstruction` and its issued FS view, the K3-B Interface
correspondence view, and, for the Prover only, one affirmative
`CheckedPlanRealizes` result. A Plan is not a view. K3-D issues a purpose-bound
adapter before source extraction or target construction. The same exact live
basis and adapter drive both source extraction and target construction, and
the checked source/proposition/validation chain retains them. Local OIR
admission remains independently source-blind and retains only its endpoint and
OIR identity.
The supplement's portable authority binding authenticates under the K3-D
source profile, but it cannot replace the live supplement bearer: omission is
`MissingDependency`, while substitution of the portable binding is `Refused`.

## Semantic-language profile boundary

The imported declaration roots have exact closures. K3-C's
kernel/property/transport/theorem-source-validation closures contain
1/7/8/9 profiles. K3-E actively selects the seven-profile property root for its
finite Analysis descriptor and observes that subject authenticating through
K1's build-once/check-many prepared-context seam; it does not execute transport
or theorem-source validation. K3-D's endpoint/source/projection/validation
closures contain 4/5/6/7 profiles, and the concrete endpoint subjects are
observed authenticating under their respective roots.

The K3-C property and K3-D validation closures intersect only at the identical
K2 Interaction, K2 Transcript/Fiat--Shamir, and K3-B Interface/Plan profile
objects. K3-B Relations belongs only to the Analysis branch. K3-D's
`RELATION_PROFILE` name denotes its endpoint-projection language, not K3-B
Relations. Supplying either branch with the union of both profile trees is
refused as an overcomplete context. Law-mutation tests check declaration-ID
rotation only; they do not execute semantics under mutated profiles.

## Falsification boundary

The matrix covers coherent construction-domain rotation, stale
Core/challenge dependents, a Relations-only witness-coordinate rename, an
Interface external-coordinate rename, an unused valid Plan export, validation
provenance/source labels, a locally valid downstream OIR mismatch,
deterministic rederivation of Analysis records, an Analysis-only proposition
change, exact profile-context closure, and profile-declaration identity
locality.

Passing this finite witness establishes only that the two owner branches
cohere over one exact root case and shared typed IDs, that K3-D retains its live
authority chain, and that the enumerated mutations have the recorded locality.
It does not establish a direct Analysis-to-OIR translation, execute a prover or
endpoint, run K3-C family transport or pointwise specialization, consume a
live Analysis specialization capability, prove the Analysis theorem, prove
projection for all endpoints, establish cryptographic security, or provide
arbitrary protocol coverage. The explicit K3-D supplement remains a residual
until its facts have durable owner-issued carriers.

Run the focused gate from the repository root:

```sh
python3 -B evaluation/k3-integrated-closure/run.py --check
```

The named-premise migration gate passes 29/29 tests. This count belongs only to
the joined witness described above; it does not include or imply a full shared
Analysis regression run.
