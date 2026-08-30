# Convergence and Promotion

> **Kind:** Temporary research-package closure record
> **State:** Complete at T2
> **Authority:** None. Durable target definitions live under `pir/`; this page
> records how the research converged and what remains deliberately unclaimed.

## 1. Closure verdict

The package objective is achieved. Source-faithful reconstructions of the
binary-field IOPCS and four materially different KZG opening/aggregation
shapes do not support one universal commitment construction. They do support
one smaller shared verifier boundary:

```text
public setup assignment
        +
ordered (commitment, query, asserted answer) claims
        +
public opening evidence
        |
        v
exact bounded verifier profile attached to an InteractiveCore
```

This is a `ConservativeExtension` at T2. It adds a separately identified
verifier profile and repairs the existing Oracle construction without changing
the meaning of `InteractiveCore`, Fresh/Fiat--Shamir interpretation, Relations,
or Analysis.

## 2. Decisions retained

1. **Claims and evidence are distinct.** A claimed value is verifier-visible
   proposition material; a proof or Merkle path is evidence for it. A wire
   codec may co-locate them but cannot make one semantically derive the other.
2. **Setup is explicit runtime public input.** The profile owns its setup-role
   schema. An invocation supplies exact `PublicParameter` values. No ambient
   registry, private advice, or setup name substitutes for those values.
3. **The common profile is verifier-side.** Honest commitment/opening
   algorithms and private material remain Plan- or construction-owned.
   Material correspondence remains Relations-owned.
4. **Evidence coverage is profile-local.** Equality-based Merkle deduplication
   is one admissible law, not the definition of all openings or multiproofs.
5. **KZG operations stay separate.** Single opening, original one-polynomial
   multipoint opening, same-point multi-polynomial aggregation, and
   independent-proof verification aggregation have different schedules,
   evidence, setup capabilities, and theorem obligations.
6. **No generic queryable object is added.** KZG does not need a private
   polynomial in verifier Core semantics. The binary-field virtual word is
   expressed per query from two ordinary Oracle answers and one derived value.
7. **Security remains downstream.** Structural admission and successful
   verifier execution establish no binding, hiding, extraction, zero
   knowledge, soundness, setup trust, or theorem transport.

## 3. Durable absorption

| Accepted result | Durable owner |
|---|---|
| verifier profile, claim/evidence types, setup binding, Core attachment, replay, and exact profile families | `pir/commitment-opening-verification.md` |
| logical-Oracle source-to-committed-Core construction, explicit producer setup inputs, and profile-local evidence coverage | `pir/oracle-commitment-construction.md` |
| domain navigation and owner boundary | `pir/README.md` and project architecture indexes |
| commitment correctness, binding, hiding, extraction, setup assumptions, BCS applicability, and quantitative loss | deferred explicit Analysis families |
| private polynomial/Oracle material, commitment grounding, and evaluation correspondence | deferred consumer-driven Relations contracts |
| exact source pins, repairs, and theorem blockers | retained temporarily in this package until documentation normalization |

No durable page depends semantically on this temporary package.

## 4. Why no new evaluator was built

The retained native FRI/IOR instrument already executes the difficult
logical-multiplicity versus physical-evidence-sharing boundary. For the new
cases, the competing architectures are distinguishable directly from their
source object graphs:

- KZG single opening has one claim and one proof;
- original multipoint KZG has one commitment, a remainder polynomial, and no
  batching challenge;
- same-point aggregation fixes all claims before a challenge and emits one
  aggregate proof;
- independent-proof aggregation fixes every proof before its coefficient and
  retains them all; and
- the binary-field IOPCS has a receipt-free virtual word and three distinct
  randomness lifecycles.

An evaluator at this point would encode these classifications rather than
resolve an execution-sensitive ambiguity. Executable promotion remains
available if implementation work later disputes an admission boundary or two
coverage laws become observationally indistinguishable.

## 5. Source repairs and inactive theorem claims

The selected binary-field operational profile explicitly records the imported
field-dimension, folding-divisibility, query-budget, and coefficient zero-fill
requirements. The stopped-one-round-early BaseFold compliance step, composed
soundness error, reusable-opening privacy, and BCS applicability remain
unproved. Those gaps do not prevent structural encoding; they prevent
activating the corresponding Analysis conclusions.

The KZG profiles bind exact setup capabilities and transcript order. They do
not prove trusted setup, binding, extraction, equivalence of aggregated and
individual openings, or Last-Challenge resistance. Those likewise remain
separate Analysis and Evidence obligations.

## 6. Closure evidence

The package closes after:

- pinned primary-source reconstruction for the binary-field and KZG families;
- equal-resolution architecture comparison and negative mutations;
- durable claim/evidence/setup/profile definitions;
- repair of the Oracle construction's universal equality-dedup assumption;
- manifest and link closure;
- the retained native FRI/IOR regression; and
- one bounded independent architecture review.

The classification is architecture-level constructive validation, not a
cryptographic implementation or theorem reproduction.

## 7. Next research package

The portfolio now advances from Oracle and commitment semantics to complete
argument organizations. The next package should study pairing-based SNARK,
inner-product argument, and polynomial-IOP organizations together rather than
redesigning their shared subcomponents independently. It should begin by
freezing how each system composes commitments, evaluation claims, reductions,
Fiat--Shamir challenges, relation grounding, and final verifier checks, then
reopen this package only if that pressure reveals a genuine verifier-boundary
contradiction.

No future package may infer that all polynomial commitments share one producer,
opening, aggregation, or security abstraction merely because they consume the
same verifier-side vocabulary.
