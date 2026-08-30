# Complete Argument Organizations

> **Kind:** Temporary cross-case research package
> **State:** Complete at the assigned T1/T2 depths
> **Authority:** None. Durable target semantics live under `pir/`,
> `relations/`, and `analysis/`. These records explain the source pressure,
> alternatives, selected encodings, repairs, and remaining obligations.

## 1. Research question

The earlier packages selected verifier-observable interaction, causal
Fiat--Shamir interpretation, logical Oracles, and exact commitment-opening
verification as separate semantic owners. This package asks whether complete
argument systems force those owners back into one universal proof object.

The pressure set is deliberately heterogeneous:

- [PLONK with one Plookup argument](plonk-and-lookup.md) combines a long
  transcript, circuit preprocessing, grand products, quotient checks, and a
  two-point KZG verification shape;
- [Groth16 over a QAP](groth16-qap.md) has a circuit-specific setup and one
  three-element proof, but no online verifier challenge;
- [Bulletproofs range and inner-product arguments](bulletproofs-inner-product.md)
  expose logarithmic recursive interaction, aggregation, and a proof package
  whose serialized order is not its semantic schedule; and
- [LogUp-GKR and Logup*](lookup-variants.md) replace Plookup's sorting and
  grand product with fractional GKR, pushforwards, and challenge-dependent
  proof advice.

The cases are studied together so that a shared abstraction is admitted only
when at least two materially different systems require the same law.

## 2. Result

The package rejects a first-class `Argument`, `ProofPackage`, generic lookup,
or universal polynomial-proof root. A complete argument is instead a checked
organization of existing owners:

```text
RelationDefinition and RelationInstance
    fixed statement and witness meaning
                |
                v
InteractiveCore + challenge interpretation
    verifier-visible schedule and checks
                |
       +--------+---------+
       |                  |
       v                  v
ProtocolInterface      ProverPlan
external package       honest construction dataflow
       |                  |
       +--------+---------+
                v
          OIR / realization
                |
                v
Analysis and Evidence
theorems, setup premises, correspondence, and losses
```

One exact verifier-side commitment-opening profile is attached only when the
operation really has ordered `(commitment, query, asserted answer)` claims and
public opening evidence. PLONK uses that boundary. Groth16 and the selected
Bulletproofs encoding do not.

One exact-use repair and one architecture candidate survive falsification:

1. A typed `PublicProverParameterDecl` Plan lane is retained as the preferred
   candidate for proving-key or prover-side SRS material that is public but
   does not affect verifier behavior. A fixed source encoding can instead
   supply a common public CRS as a Core `PublicParameter` or embed a fixed
   value in a Plan. The candidate preserves a minimal verifier Core and makes
   Plans reusable across setup outputs, but the reviewed sources do not force
   it for expressibility.
2. The canonical-framed Fiat--Shamir construction must require at least one
   Core challenge. Otherwise a zero-challenge protocol such as Groth16 can
   acquire arbitrarily many FS identities that transform no challenge while
   adding only transcript work, cost, and noncompletion surface.

The canonical-FS repair is promoted now. The Plan candidate is deliberately
deferred: accumulation research has exposed a second Plan lifecycle question,
and changing the Plan body would rotate several dependent profiles. Both Plan
questions should be co-designed and promoted, rejected, or revised in one
owner-consistent change. Neither proposal changes `InteractiveCore`, Relations
satisfaction, commitment-opening verification, or Analysis property meaning.

## 3. Case disposition

| Case | Assigned depth | Result | Shared-model effect |
|---|---:|---|---|
| PLONK + Plookup | T2 | `ProfileOrModule` | Exercises exact two-point KZG use; motivates a deferred reusable public prover-parameter candidate but no new argument root |
| Groth16/QAP | T2 | `Native` | Supplies the zero-challenge FS exact-use counterexample; separately motivates a conservative shared lifecycle improvement for reusable minimal-verifier Plans |
| Bulletproofs range + IPA | T2 | `Native` | Confirms flat finite Core, explicit reductions, and Interface/OIR proof packaging |
| LogUp-GKR + Logup* | T1 | `Native` within finite v0 limits | Confirms challenge-dependent Plan advice, existing shared-challenge law, and exact PCS attachment |

`ProfileOrModule` means protocol-specific content is required under existing
shared grammar. `ConservativeExtension` means one owner-local shared grammar
addition is required without changing admitted old meanings. `Native` means
the active shared grammar is already sufficient. None of the classifications
is an implementation-support or security claim.

## 4. Package pages

| Page | Role |
|---|---|
| [PLONK and Plookup](plonk-and-lookup.md) | Pinned sources, fixed relation, complete schedule, proof package, two-point KZG use, mutations, and theorem boundary |
| [Groth16 and QAP](groth16-qap.md) | QAP/setup graph, zero-challenge schedule, proving material, pairing check, and setup-correspondence boundary |
| [Bulletproofs and Inner Product](bulletproofs-inner-product.md) | Aggregated range schedule, IPA reductions, finite unrolling, packaging, and realization-specific deviations |
| [Lookup Variants](lookup-variants.md) | LogUp-GKR and Logup* deltas, pushforward advice, shared challenge, pole premises, and source defects |
| [Architecture Selection](architecture-selection.md) | Cross-case candidate comparison, accepted repairs, rejected roots, and reopening conditions |
| [Convergence and Promotion](convergence-and-promotion.md) | Closure judgment, durable absorption, bounded validation, nonclaims, and next package |

## 5. Evidence boundary

The PLONK, Groth16, and Bulletproofs records are constructive T2 encodings: an
exact representative object graph and verifier schedule are mapped to the
target owners. Each now fixes one finite member schema, symbolic identity-
dependency equations, complete owner/construction ordering, grounding
obligations, qualified failure partition, intrinsic resource envelope, and
typed negative mutations. Symbolic names denote exact fixed finite values or
identities within the selected member; concrete octets and executable replay
remain T3. The lookup-variant record is T1: its sources omit enough transcript
and PCS detail that a full T2 encoding would invent rather than recover
semantics.

No new evaluator is justified. The remaining disagreements are visible in
the static owner graph and schedule; an executable probe would merely encode
the selected classification. Existing PLONK and LogUp fixtures remain current-
implementation pressure only and are not promoted to support claims.

## 6. Deletion trigger

Delete this package only after accepted shared laws and scope boundaries have
been absorbed into durable owners, protocol-specific profiles have stable
homes, the portfolio retains the final classifications and nonclaims, and no
durable page depends on these temporary records.
