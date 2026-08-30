# Convergence and Promotion

> **Kind:** Temporary package-closure and durable-promotion record
> **State:** Complete; final gates and independent review passed
> **Authority:** None. Durable owners define accepted target semantics. The
> reviewed paper owns its construction and theorem statements; this record
> neither repairs nor validates those theorems.

## 1. Result

The package achieved its representability and architecture objective after
refining two ownership boundaries exposed by the research. zkc can represent
the reviewed duplex-sponge transform over one unchanged
public-coin `InteractiveCore` without weakening the canonical-framed
Fiat--Shamir construction and without moving salt, transcript state, or theorem
assumptions into the source interaction.

The refinement is intentional: PIR proves exact Statement/message occurrence
and evaluation coverage, while encoder injectivity is a separate source-
correspondence or Analysis premise; PIR prepares and replays a supplied salt,
while honest salt generation remains Plan/Realization work. The package closes
those boundaries explicitly rather than claiming that structural admission
establishes either property.

The selected target is:

```text
                         InteractiveCore
                        /       |        \
                       /        |         \
                  Fresh   canonical FS   duplex FS
                             profile       profile
                                |             |
                        typed framing    Start_h(instance)
                        namespace/retry  proof-carried salt
                        bounded failure  overwrite duplex
```

The same `CoreId` can therefore have three pairwise-distinct Protocol
identities. Each Fiat--Shamir family owns its complete construction,
admission, execution, receipt, replay, failure, and source-view law. Neither is
a mode, fallback, or implementation of the other.

The case remains a `ConservativeExtension`: it adds one closed sibling family
and one typed runtime-material seam while preserving existing Core and
canonical-framed meanings. It does not require a generic transcript program,
caller-authored action map, or universal transition algebra.

## 2. Why this is the narrowest coherent design

The source differs from the canonical-framed family in identity-bearing ways:

- initialization hashes a runtime binary instance rather than using a fixed
  construction state;
- one proof-carried salt precedes every prover message but is not a source-Core
  event;
- absorption overwrites raw fixed-length encodings with lazy boundary
  permutation;
- challenges use one total decode with no namespace, retry, or semantic
  sampling failure; and
- proof generation needs only the challenge prefix before the final prover
  message, while verification executes the final transition.

Adding a mode to the existing construction would make incompatible fields
appear optional and would blur theorem subjects. A generic operation program
would transfer schedule and influence authority to the caller. A single common
Fiat--Shamir profile importing every construction family would rotate old
subjects whenever a new family appeared. Closed sibling profiles avoid all
three failures while sharing the actual invariant: challenge resolution over
an immutable Core.

Construction-selected modules and algorithms remain useful below the family
boundary for exact hashes, permutations, encoders, and decoders. They do not
decide which source events enter the transcript or when a challenge succeeds.

## 3. Exact semantic disposition

The accepted duplex family owns:

1. a finite alphabet, positive rate, capacity, state and instance bounds;
2. exact hash-to-capacity, forward-state-operation, encoder, and decoder uses;
3. a fixed canonical projection of root-initial Statement bindings to the
   binary runtime instance;
4. one public construction-material salt coordinate;
5. one unconditional message/challenge pair per source round;
6. exact `Start`, overwrite `Absorb`, and atomic `Squeeze` laws;
7. verifier-complete and prover-required schedules;
8. profile-specific receipts and deterministic replay; and
9. a same-Core Fresh/duplex structural checking result.

The actual Statement values, salt, messages, states, receipts, proof bytes,
provider paths, source references, theorem results, and evidence are not
construction identity. The selected profile and exact static algorithm and
codec coordinates are.

Construction material is a typed runtime satellite. It is neither a Core
input nor a synthetic prover message. Its capability is prepared against the
exact Protocol, construction, invocation, evaluator, and salt value before
execution, then retained by the duplex resolver. This preserves the source
Core while preventing an untyped ambient prefix.

## 4. Source and theorem disposition

The operational state machine is coherent and independently reproducible. The
reviewed source's security proofs are not activated. The audit found four
unresolved source-level issues:

1. the lazy operational permutation schedule conflicts with exact call counts
   and backtracking offsets later used in the proof;
2. the codec definition omits decoder-fiber operations required by later
   reductions;
3. the claimed zero-distance fiber hybrid is false for unequal fibers unless
   an additional bias is charged or balanced fibers are required; and
4. the displayed fixed salt bit length is not a natural length for general
   non-power-of-two alphabets.

These findings do not justify changing `Start`, `Absorb`, or `Squeeze` to make
the proof prose fit. They require a repaired theorem, an exact restriction, an
erratum, or an independent proof. Until then, soundness, knowledge soundness,
zero knowledge, state restoration, ideal-permutation realization, query loss,
and salt-distribution applicability remain `CannotAnswer`, `Refused`, or
`Unsupported` under their exact missing premise.

## 5. Durable absorption map

| Durable owner | Accepted change |
|---|---|
| `pir/interactive-core.md` | Construction-selected Protocol profiles, family-dispatched resolver receipts and failures, and runtime-material-aware resolver preparation |
| `pir/fiat-shamir.md` | Canonical-framed sibling identity and an exact refusal to claim duplex correspondence |
| `pir/duplex-sponge-fiat-shamir.md` | Closed operational duplex construction family at the current target granularity, with lifecycle, execution, replay, source views, and nonclaims |
| `pir/canonical-pir.md` | Profile-specific external construction authentication without changing the Core/Protocol root shape |
| `pir/interfaces-and-plans.md` | Canonical-only active support and the reason pre-execution salt needs a separate downstream satellite |
| `pir/endpoint-projection-views.md` | Early typed `Unsupported` for duplex endpoints |
| `analysis/` | Canonical-only active theorem catalog and explicit duplex source-validation blockers |
| `oir/` | Canonical-only projection support and the missing duplex proof-material contract |
| `project/` | Sibling-family architecture, manifest route, and support boundary |
| `evaluation/duplex-sponge-transcript/` | Retained finite transition, admission, identity, provenance, mutation, and replay falsifier |

No durable page depends on this temporary package. The temporary pages retain
the source ledger, rejected alternatives, evidence interpretation, and closure
history until the broader redesign is consolidated.

## 6. Implementation gap and migration order

This work defines a target and finite research evidence; it does not claim a
production implementation. A later implementation should proceed in this
order:

1. publish complete reconstructible language-profile preimages and freeze the
   canonical-framed and duplex profile IDs;
2. authenticate profile-specific construction bodies in the canonical PIR
   carrier and preserve exact family dispatch at Protocol formation;
3. implement construction-material preparation, resolver capability binding,
   family receipts, complete execution, and replay;
4. add an Interface proof-material assignment and a pre-execution material
   Plan only when a concrete endpoint is selected;
5. add a sibling OIR projection owning proof tuple parsing, salt placement,
   message wire codecs, and correspondence to distinct transcript codecs;
6. bind concrete providers in Realization and record conformance evidence; and
7. activate a cryptographic Analysis family only after the source theorem or
   an independent replacement is validated.

Each step has an explicit `Unsupported` or missing-dependency boundary before
its owner exists. Partial downstream support must not be inferred from PIR
construction admission.

## 7. Executable result

The retained finite evaluator uses a three-round source-shaped Core, one
proof-carried salt, zero- and nonzero-length codecs, and a small exhaustive
state space. Two separately written transition relations agree on the frozen
trace and selected edge domains. The mutation suite rejects wrong empty,
boundary, overwrite, output-continuation, salt-order, challenge-reabsorption,
codec-map, decoder, identity, and replay behavior.

The final reproducibility commands and exact counts are recorded in the gate
table below. Their success establishes finite falsification evidence only, not
cryptographic security or durable runtime conformance.

## 8. Portfolio disposition and next package

The duplex case is promoted from constructive encoding to executable
falsification because empty absorption, partial squeezing, and lazy boundary
permutation left materially different prose implementations plausible. The
promotion is evidence-driven, not a new default depth for every case.

The portfolio order does not need revision. Interaction/Fiat--Shamir and
algebraic-reduction pressure are now complete at their selected depths. The
next large package should be **Oracle and Polynomial-Commitment Semantics**:

```text
retained native FRI/IOR baseline
              |
              v
binary-field hiding PCS variant
              |
              v
single and batched KZG
              |
              v
cross-family construction/setup/opening boundary
```

The package should retain the completed native FRI/IOR case as a fixed
baseline, reconstruct the hiding binary-field PCS variant first, then KZG
single and batched openings, and compare both before promoting a shared
abstraction. Its central question is:

> Can one checked logical-Oracle-to-commitment architecture represent both a
> transparent hiding binary-field PCS and an SRS/group/pairing KZG family
> without duplicating setup, claim, challenge, opening, or verification
> authority?

The default evidence depth remains constructive. Executable promotion occurs
only if competing semantics, an execution-sensitive rejection boundary, or a
self-fulfilling workaround survives the source and architecture comparison.
This combines the already-ordered variant and KZG cases into one sufficiently
large research package; it does not redo the retained FRI work.

Do not make duplex theorem activation the next package: the source proof is
currently blocked. Do not make duplex endpoint integration next either: no
second endpoint consumer has yet justified a shared material/serialization
law. Do not interrupt portfolio coverage with Sumcheck/GKR property Analysis
unless quantitative theorem applicability becomes the explicitly selected
research question.

## 9. Closure gate

| Gate | State |
|---|---|
| Primary-source and comparator reconstruction | Passed |
| Equal-resolution architecture candidates | Passed |
| Construction body, identity topology/dependency partition, lifecycle, runtime material, execution, receipts, replay, and source views | Passed |
| Complete profile preimages and persistent profile/subject IDs | Deferred explicitly to semantic freeze; no persistent ID claim |
| Canonical-framed non-regression and family separation | Passed: canonical-framed 81/81 and duplex identity/locality cases |
| Finite independent relation and named mutations | Passed: duplex 59/59, strict frozen replay, and generation-support boundary check |
| Durable absorption and manifest/link closure | Passed: manifest, scoped links, public-tree guard, and diff check |
| Current-to-target implementation gap | Passed |
| Portfolio disposition and next-package contract | Passed |
| One independent bounded closure review | Passed with no release blocker |

The retained executable report is `sha256:26c6a7fc17d5e466f539896a07ae86c826e73fdd01c5a081efd5a7f8f4f7566a`.
The generation-support check reconstructed the frozen proof, simulated exactly
the first two challenge occurrences, and kept proof generation, prover
necessity, entropy uniformity, and portable identity explicitly false.

A future failed gate reopens the smallest owning boundary; it does not trigger
an unbounded review loop after the identified defect is repaired.

## 10. Reopening conditions

Reopen the duplex family if an exact source requires conditional rounds,
joint challenges, verifier messages, Oracle effects, runtime labels, secret or
mutable construction material, or a different prover/verifier prefix law.

Reopen the sibling-profile choice only if a closed Foundation contract can add
top-level construction families with the same identity locality and without
an opaque schedule callback.

Reopen the theorem boundary only after exact source repair or an independently
validated replacement theorem. Reopen downstream support only for a concrete
consumer whose proof-material and serialization requirements can be specified
without changing the operational construction.
