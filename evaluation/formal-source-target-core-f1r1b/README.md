# F1-R1B exact-target Core carrier and admission witness

This bounded evaluator forms and admits one complete fourteen-field target
`InteractiveCore` plus its two-field Fresh `Protocol` under the frozen target
Interaction profile. It is an executable research falsifier, not a compiler
component, durable PIR evaluator, implementation-conformance result, formal
proof, cryptographic-security result, or Q1 source-correspondence result.

Run the focused gate from the repository root:

```sh
python3 -B evaluation/formal-source-target-core-f1r1b/run.py --check
```

Use `--json` for the complete result and measurements.

## Exact positive subject

The admitted Core is a finite additive Schnorr-shaped interaction over
`Z/3Z`:

```text
public statement Y
  -> Prover commitment A
  -> independent Fresh challenge c
  -> Prover response z
  -> Check: z = A + cY mod 3
  -> guarded Accept
  -> unconditional Reject
```

All fourteen target Core fields are present. Families not used by this subject
are encoded as exact empty sequences. The subject uses one authenticated
semantic module for two message-channel declarations, one challenge-domain
declaration, and one public-coin-law declaration. The K1 portable Check has
the exact `(Z3,Z3,Z3,Z3) -> Bool` ABI and empty failure row. A separate K1
Boolean-identity algorithm guards the accepting terminal.

The finite equation is useful because it is executable and exhaustive without
pretending to be a cryptographic group. A separately written interpreter
checks all 81 input tuples. The K1 evaluator separately authenticates and
evaluates one true and one false sample.

The frozen target identities are in
[`expected-identities.json`](expected-identities.json). The principal roots
are:

| Coordinate | Identity |
|---|---|
| Interaction profile | `zkcidv0:foundation.semantic-language-profile:f21774d19ebf5e045b1d5c70f9bd0ee1c7eb1202dc11f948900eb067e102ce87` |
| semantic module | `zkcidv0:foundation.semantic-module:de7f837dc849ff52fb045259839dfb9efde015a65781ad064feb5a91b0ae29b7` |
| Schnorr Check algorithm | `zkcidv0:foundation.portable-algorithm:86a47a88f56ed94a258b1e8215ec9b4f4537265f435bf32f7569d05f725722df` |
| target Core | `zkcidv0:pir.interactive-core:33f9d34abd61e22565b85fbfe03a35b3ca55f1a3980b71c5e9b729b3a93027f5` |
| Fresh Protocol | `zkcidv0:pir.protocol:5ef61d48cca624e042b89fdd56935c3e9137a0790a2625ce2dd4f7da9ca92f94` |

The profiled Core body is 8,179 octets. The intentionally expanded portable
algorithm preimage is 179,147 octets and remains below K1's body bound.

## What the gate checks

[`reference_model.py`](reference_model.py) compiles the complete Appendix-A
carrier and runs all ten admission stages applicable to the selected slice:

1. one-ledger authentication of the prior-meta basis, target profile, Core,
   exact-used module closure, algorithms, algorithm module closures, and
   evaluation contract;
2. exact carrier, bounds, reference, and supported-constructor checks;
3. derived `DirectOwnerModules`, exact-used equality, nominal declaration
   resolution, and exact algorithm/contract closure;
4. K1 value-type and total Boolean ABI checks;
5. rooted scopes, binding coverage, and prefix availability;
6. one-to-one Challenge, Check, and Terminal occurrence backlinks;
7. public Challenge-condition visibility;
8. independent/exclusive challenge-policy checks;
9. initial-claim and terminal/check closure for the supported fragment; and
10. the unconditional final fallback before minting an admitted handle.

Fresh formation accepts only the identical process-local admitted Core handle,
reauthenticates its target profile and Protocol body, and refuses a bare Core
record or a different Core ID. The research handles are deliberately
nonserializable. This models the target lifecycle; it is not a Python security
boundary or current compiler authority.

[`independent.py`](independent.py) separately implements the complete Core and
Protocol body encoders. It shares K1's constitutional datum/value machinery
and the typed research carrier, but it does not call the reference body
compiler. It agrees on the positive Core, six additional carrier shapes that
exercise otherwise empty field families, and the Fresh Protocol. This is
bounded encoder-diversity evidence, not an independent implementation of
admission.

## Current bounded result

The gate passes **27/27 exact expected cases**:

- 7 affirmative controls: target Core, Fresh Protocol, frozen identities,
  independent body encoding, exhaustive finite equation, K1 evaluation
  samples, and process-local handle behavior;
- 19 exact nonaffirmative mutations covering retained IDs, missing/extra
  exact-used modules, missing preimages, declaration kind and ABI mismatch,
  scope opening, three backlink families, future reads, private Challenge
  conditions, invalid Shared policy, unresolved claims, fallback omission,
  target-profile substitution, Protocol/Core substitution, bare-record
  authority substitution, and retained Protocol ID; and
- 1 explicit `Unsupported` result for a well-formed target family outside the
  evaluator's selected fragment.

Every mutation requires one exact outcome and local code; “any failure” is not
accepted.

## Exact boundary and next gate

This is a complete target carrier and a bounded admission evaluator for the
named subject, not a complete implementation of every `core-admission-v0`
constructor. Constants, derived values, Oracles, reductions, module effects,
joint coins, general claim paths, and several nested-scope cases remain
fail-closed or outside the positive fragment. In particular:

- a nominal challenge-domain or public-coin-law coordinate does not prove a
  distribution or cryptographic property;
- no strategy, resolver, invocation, execution, replay, or relation is run;
- the gate does not implement `PublicCoinView` or establish FS eligibility;
- no owner static view, exact read closure, Relations root, correspondence,
  package, provider artifact, theorem, Compiler preservation result, OIR
  projection, or realization is established; and
- the offline handle is issued by this research evaluator, not by current zkc
  implementation authority. Q0 and Q1 therefore remain open.

The subsequent
[`F1-R1C0 determinacy audit`](../formal-source-owner-views-f1r1c/README.md)
retains these identities and admitted handles but returns
`CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`. The authenticated target source
names all six owner views, yet the profile does not publish the promised closed
schema catalog, exact nested body grammars, field-to-law bindings, and complete
authority-envelope bodies needed to derive a target read manifest without
guessing. This is the F0-reopening branch, not ordinary evaluator plumbing.
F0-V must repair and republish that owner contract before R1C resumes with the
same admitted-handle lifecycle.
