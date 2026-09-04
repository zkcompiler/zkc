# Accumulation and Recursion Research Contract

> **Kind:** Temporary frozen research contract
> **State:** Frozen before case-level convergence
> **Authority:** None. This page fixes research scope and evidence discipline;
> it does not preselect a semantic result.

## 1. Decision question

Determine the smallest coherent target architecture that can represent exact
finite folding, accumulation, IVC/NIVC, and imported-verifier cases while
preserving:

- one verifier-observable execution as one flat finite `InteractiveCore`;
- occurrence-exact relation instances, claims, reductions, and witness
  evolution;
- separate Protocol, Plan, Relations, Analysis, Interface/OIR, and Evidence
  authority;
- strong target transcript binding even when a source uses a weaker
  Fiat--Shamir convention; and
- acyclic semantic identities for recursive verification.

The package may reopen those points if a source-faithful counterexample makes
one impossible. Passing existing boundary tests is not a reason to stop
generative comparison.

## 2. Primary sources and revision discipline

The initial source set is:

| Case | Primary source | Frozen intake |
|---|---|---|
| Nova | [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370) | current revision dated `2024-07-20`, PDF SHA-256 `2a912c9715d0c8a6ae573addedb1d77643c5540e3968a95a9d82059dee0bf6e1` |
| corrected cycle-based Nova | [Revisiting the Nova Proof System on a Cycle of Curves](https://eprint.iacr.org/2023/969) | revision dated `2023-06-20`, PDF SHA-256 `f2118e5a04bd226e367639b2e8c4128eca71f1c903af450452a82de57f8c48d8` |
| HyperNova | [HyperNova: Recursive Arguments for Customizable Constraint Systems](https://eprint.iacr.org/2023/573) | current revision dated `2026-02-20`, PDF SHA-256 `08fdc3b155a9b681baecb48aad26993f53c0cb08511c0771154bd5a349761572` |
| ProtoStar | [ProtoStar: Generic Efficient Accumulation/Folding for Special-Sound Protocols](https://eprint.iacr.org/2023/620) | revision dated `2023-12-21`, PDF SHA-256 `e93bc711df7bc2e733d446f1f273c5d2bc9d769da2f2e4643f2bc506e87d0509` |
| LatticeFold+ | [LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems](https://eprint.iacr.org/2025/247) | archive revision dated `2025-08-10` (PDF title page `2025-08-09`), PDF SHA-256 `48f40d28f42978236d7fcaa335022d124df76061ef48ccbd400127e7eb130ea1` |
| recursive import | BCTV [Scalable Zero Knowledge via Cycles of Elliptic Curves](https://eprint.iacr.org/2014/595), BCCT [Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data](https://eprint.iacr.org/2012/095), and [Fractal](https://eprint.iacr.org/2019/1076) | archive revisions `20200618:063504`, `20121228:123450`, and `20200715:141732`; PDF SHA-256 values `e5e32ca3713b1747681f9f194359023a7c0ec842f293b84793fa924c0faad62e`, `c29188804166b6f2d1ec2753b119e29e0b0af942e6bff8971b0e8d4c911e56ed`, and `d152c8d0d625a1ffb7cd3ad86ccc410b4dfa8f77aea82309dde1e8824236fb42` respectively |

The case records must distinguish paper revisions, corrections, implementation
profiles, and inferred errata. A later source revision cannot silently replace
the frozen intake. If a source contains a known unsound or underspecified
construction, the target records the defect and selects no theorem from it.

## 3. Required semantic distinctions

Every case must answer these questions explicitly:

1. What are the input relation-instance occurrences, input witness
   occurrences, output accumulator instance, and evolved private witness?
2. Is the operation a proof of both inputs, a fold preserving an invariant, an
   accumulation step, an IVC transition, a decider, or a composition of those?
3. Which messages and challenges are verifier-observable Core occurrences, and
   which calculations belong only to honest Plan construction?
4. Does a private value have to be derived after the final Challenge even when
   the Core has no subsequent Prover decision?
5. Which public setup or proving material is consumed by Plan but intentionally
   absent from a minimal verifier Core?
6. How is the output instance occurrence connected to the next step's input
   claim without equating equal-valued but causally distinct occurrences?
7. Which commitments use an exact verifier-side opening profile, and which are
   merely algebraic values or ordinary Core checks?
8. Which source transcript coordinates are too weak for the target strong-
   binding policy, especially omitted input instances or accumulator state?
9. Where do zero knowledge, blinding, compression, and final decision remain
   separate wrappers or Analysis properties?
10. Does recursive verification consume a finite imported verifier semantics,
    proof bytes, a checked projection, or an ambient implementation callback?
11. What breaks the apparent cycle among an outer relation, imported verifier,
    inner Protocol identity, and recursively produced proof?
12. Which resource and depth bounds are fixed by one finite member, and which
    statements require an Analysis family rather than Core execution?

## 4. Candidate space

At equal resolution, compare at least:

1. **Existing owners only:** ordinary decision recipes, reductions, relation
   transforms, and persistent Plan state.
2. **Artificial final message:** add a semantically empty Prover publication
   solely to create a final decision point.
3. **Plan completion recipes:** allow a bounded private Plan derivation at
   successful Core completion, with no verifier-visible effect.
4. **General post-challenge callbacks:** permit opaque producer work after any
   Challenge.
5. **Accumulator root:** add a universal PIR accumulator/folding subject.
6. **Checked authoring construction:** introduce a separately admitted static
   elaboration only when repeated finite bodies require it.
7. **Recursive child execution:** let one Core invoke another Protocol at
   runtime.
8. **Imported verifier relation:** represent finite inner-verifier semantics as
   typed outer relation material and separately check correspondence.

The package must also compare native Core/common-parameter and fixed Plan-
constant controls against the deferred typed public prover-parameter lane.

## 5. Evidence depth

`P09`, `V04`, and `P10` target strict T2. Every retained T2 case must contain:

- an exact finite member schema and fixed dimensions;
- complete typed owner and symbolic identity dependency tables;
- exact Core schedule, Challenge interpretation, Plan graph, Interface/OIR
  projection, Relations bindings, and relevant verifier profiles;
- input/output occurrence and grounding equations;
- construction/composition order with no circular authority;
- a complete qualified failure partition;
- finite intrinsic bounds and explicit family-level nonclaims; and
- representative mutations that distinguish every competing architecture.

Source omissions may force T1 or `Undetermined`; the record must say so rather
than inventing transcript, PCS, setup, or theorem semantics.

## 6. Promotion rule

A shared grammar change may be promoted only when:

1. at least two materially different cases require the same owner-local law,
   or one case exposes a direct contradiction in an existing shared contract;
2. the existing native and specialized controls are stated honestly;
3. the change has exact identity, admission, execution, replay, and failure
   semantics;
4. every dependent owner affected by the identity rotation is reconciled in
   the same checkpoint; and
5. a bounded falsification pass finds no remaining authority cycle or silent
   semantic side effect.

Convenience, API similarity, or implementation reuse is insufficient.

## 7. Exit criteria

The package closes only when:

1. every named case has exactly one primary classification and achieved depth;
2. folding, accumulation, IVC/NIVC, decider, compression, and recursive import
   are not conflated;
3. the Plan public-parameter and completion questions are selected, rejected,
   or explicitly deferred with a concrete blocker;
4. input/output relation and witness occurrences have an exact causal bridge;
5. weak source transcript conventions cannot enter as target strong-FS facts;
6. recursive identity is acyclic and imported semantics cannot be supplied by
   an ambient callback;
7. accepted shared laws are absorbed into their durable owners and no durable
   page depends on this package;
8. status and portfolio cursors are normalized once; and
9. local links, inventory ownership, whitespace, public-tree hygiene, and the
   bounded relevant regression checks pass.

An integrated review follows this cluster. Repeated global review after every
paper is explicitly outside the work contract unless a fundamental
obstruction appears.
