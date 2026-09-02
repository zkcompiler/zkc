# F1-R0 Reference Package and Independent-Checker Feasibility

> **Kind:** Temporary F1 executable-feasibility result and sequencing repair
> **State:** F1-R0 package/checker boundary complete at bounded reference
> resolution; F1-R1A target profile/source basis is now complete at bounded
> resolution, while F1-R1B/R1C/R1D, live-owner F1-I, and all F2 stages remain
> open
> **Authority:** None. This result changes no current or target semantic
> definition, artifact identity, admission result, Analysis judgment,
> implementation claim, or roadmap priority.
> **Evidence:** The focused evaluator under
> [`evaluation/formal-source-package-f1r/`](../../../../evaluation/formal-source-package-f1r/README.md)
> passes 18/18 fixed cases with two independently implemented checkers.

## 1. Question and exact disposition

F1-R0 asks a narrower question than full Q1 source correspondence:

> Can the provisional two-layer package class carry complete authentication
> preimages plus an exact question-relative read closure, and can two
> independently implemented consumers discriminate the F0 mutation set
> without trusting the producer or sharing a parser/canonical encoder?

For the bounded manual subjects, the answer is **Affirmative**. This supports
the feasibility of the F0 A/S/C topology and sharpens its minimum contract.
It does not answer whether any package corresponds to an admitted live zkc
subject.

The original F1-R entry contract also asked for the selected target's exact
canonical bodies. That stronger premise is not currently available. The live
[K2 evaluator](../../../../evaluation/k2-protocol-fiat-shamir/README.md)
explicitly states that most of its bodies are fixture-exact or
behavioral-shape witnesses, that its profiles are witness-local rather than
the published target profiles, and that its finite body encoders are not the
durable target body compilers. The
[K3-E joined witness](../../../../evaluation/k3-integrated-closure/README.md)
reuses that same K2/K3-B/K1 chain and explicitly does not add another
semantics implementation. Substituting those IDs for target IDs would
therefore be a false conformance claim.

F1 is consequently split more precisely:

```text
F1-R0  package/checker and mutation feasibility over manual target-shaped data
  -> F1-R1A  exact target profile/source basis
  -> F1-R1B  exact target carrier/admission
  -> F1-R1C  exact owner views/read closure
  -> F1-R1D  exact integrated target package
  -> F1-I   live admitted-owner issuance and authority binding
  -> F2-O/P/D
```

This is a sequencing repair, not a reversal of the two-layer architecture.
No missing `InteractiveCore` field or owner boundary was found.

## 2. Executable construction

The temporary package has two authenticated logical layers:

```text
authentication closure
  roots + every dependency preimage + recursively recomputed IDs

question-relative projection
  exact read fixed point
  + protected-observation-to-read total map
  + one-to-one source-node/pointer ledger
  + independently reselected values
```

Every fixture-only profile is explicitly namespaced `f1r-manual-*`; none can
be confused mechanically with a published target profile.

The untrusted producer emits three bounded subjects:

| Subject | Role in F1-R0 | Important observations |
|---|---|---|
| Fresh Schnorr verifier | Required positive package | public statement, public coin, effects, claim reduction, execution/failure/terminal, relation definition/model/instance, Protocol correspondence |
| interleaved two-reduction Schnorr with one shared challenge | structural discriminator | one global order, one challenge occurrence, two exact reduction uses, equal-value alias resistance |
| canonical FS Schnorr | security-motivated discriminator | statement and commitment transcript influence, challenge domain/space, sampling failure, occurrence order |

The Fresh package contains no `ProverPlan`, live witness value, confidential
carrier, mutable state, or causal capability. The auxiliary packages do not
broaden the success claim; they prevent a simple alternating Schnorr fixture
from vacuously passing shared-challenge, interleaving, and transcript-omission
tests it cannot express.

The checker pair is intentionally asymmetric:

- the Python checker uses the standard-library JSON decoder and SHA-256 but an
  independently written schema, canonical encoder, dependency closure,
  selector, and result constructor; and
- the standalone Rust checker has no crate dependencies and separately
  implements strict JSON, canonical encoding, SHA-256, dependency closure,
  JSON Pointer selection, and result construction.

Neither checker imports or invokes the exporter. They share the written
temporary contract, as any conforming implementations must, but no parser or
canonical encoder.

## 3. Bounded result

Both checkers reproduce byte-identical checker-independent agreement bodies
for all three positive packages. The frozen Fresh controls are:

| Value | Identity |
|---|---|
| contract | `sha256:008da473e9269f2881bbcd1cc7ae8ae38fa7b758d4e2d88f512686671dedccfe` |
| closed manifest | `sha256:83b591a623c27bab62573a223e6768633df832ae6ab0f48a19ebc7c74b2c8b0e` |
| package | `sha256:47df9f9a435f46894d4f2293768def9be2b3f414746f95cdfa7d6f1195d68b2e` |
| formed proposition | `sha256:5a0cedb2ac9572c1bd63fe4663a3b9e9081490dfd99f78ddcfc582d5629b17da` |
| common result | `sha256:5f488dc4c64940c6bd52812e8a65b4b290f24e403821d83cf4c9e7e0ab6bab91` |

The 15 negative/boundary cases have exact expected classes and local stable
codes:

| Boundary | Result |
|---|---|
| changed root body with retained source ID | `Negative/F1R-N-AUTH-ID` |
| omitted required order/read dependency | `Negative/F1R-N-MISSING-READ` |
| phantom provider read | `Negative/F1R-N-EXTRA-READ` |
| equal-typed/equal-valued occurrence alias | `Negative/F1R-N-COORDINATE-BINDING` |
| one shared challenge replaced by two equal-valued draws | `Negative/F1R-N-SHARED-CHALLENGE` |
| reordered interleaved occurrences | `Negative/F1R-N-EXECUTION-ORDER` |
| cross-profile replay | `KindMismatch/F1R-K-PROFILE` |
| omitted FS commitment transcript input | `Negative/F1R-N-MISSING-READ` |
| confidential value or causal capability serialization | `Refused/F1R-R-EXCLUDED-SUPPORT` |
| duplicate JSON key | `Malformed/F1R-M-DUPLICATE-KEY` |
| changed bytes with retained package ID | `Negative/F1R-N-PACKAGE-ID` |
| protected observation not covering every required read | `Malformed/F1R-M-OBSERVATION-COVERAGE` |
| two contract reads aliasing one source coordinate | `Malformed/F1R-M-ALIASED-SOURCE` |
| dormant read-catalog row outside the required fixed point | `Malformed/F1R-M-READ-CLOSURE` |

The executable count and IDs belong only to this exact frozen corpus. The
checked-in positive identity table is a drift sentinel, not proof of its own
semantic adequacy.

## 4. Contract refinements learned from F1-R0

### 4.1 Protected observations need a total read map

F0 named a protected-observation catalog, but a list of names cannot establish
which source facts are required. F1-R0 therefore requires:

```text
ProtectedObservation -> nonempty exact read set
union(all protected read sets) = required-read fixed point
```

An unknown, missing, or uncovered read makes the contract malformed. This
turns “preserve challenge correlation” from prose into an auditable source
closure without making the package an owner of challenge semantics.

### 4.2 The catalog itself must be closed and alias-free

The read catalog must equal the fixed point reached from the contract's read
roots. Dormant rows are not harmless extensibility: they create observations
whose inclusion policy is unspecified. Distinct read coordinates must also
bind distinct `(source node, source pointer)` pairs. Equal selected values do
not weaken this condition.

### 4.3 Package agreement and qualified Analysis evidence remain distinct

The common result binds the exact contract, package, root IDs, manifest,
semantic profile, and `ExactSemanticReadAgreement` direction. Checker identity
remains in the outer execution envelope so two implementations can agree on
one semantic body.

A durable checked result must go further: its Analysis validation basis must
name the checker implementation/ABI, decoder and canonical rules, finite
controls, source/environment bindings, residual trust, policy, and cold-replay
requirements. A caller must pin the proposition it requested. A coherent
package for another profile can be valid for another proposition without
being substitutable for this one.

## 5. Assurance-lattice position

| Level | F1-R0 result |
|---|---|
| Q0 source admission | not formed; manual values carry no owner authority |
| Q1 exact admitted-source reification | **open**; F1-R0 establishes only package/checker feasibility and internal exact agreement |
| Q2 provider correspondence | not started |
| Q3--Q6 theorem environment, truth, applicability, property | not started |
| Q7--Q10 transition, transport, OIR, realization | not started |

It would be incorrect to relabel the common `F1R-AFFIRMATIVE` record as an
Analysis `Affirmative` Q1 result. No source authority entered the evaluator,
and no capability can be minted from its bytes.

## 6. Staged F1-R1 and F1-I entry contract

The complete F1-R1 sequence succeeds only when the exact bounded target source
can be formed without substituting fixture-local profiles or hand-authored
identities. It needs:

1. the exact published target semantic-profile closure selected for the
   bounded Fresh Schnorr source;
2. the durable canonical body compiler and admission evaluator for the exact
   `InteractiveCore`, Fresh `Protocol`, relation definition/model/instance,
   and Protocol-correspondence bodies;
3. exact owner view evaluators for `PublicBindingView`, `PublicCoinView`,
   `EffectView`, `ClaimReductionView`, and Protocol `ExecutionView`;
4. an exact formal-source contract whose observation/read map is issued or
   independently reconstructed from those owners; and
5. two checker paths that reproduce the target root IDs and package result,
   with the F1-R0 corpus retained as a compatibility and mutation control.

The subsequent
[`F1-R1A target-basis gate`](f1r1a-target-basis-and-admission-gap.md) closes
only item 1 and the source-declaration part of items 2 and 3. It independently
reconstructs the frozen target Interaction profile and demonstrates that K2's
witness-local profile, eight-field Core, and recursively relabelled IDs cannot
substitute for target admission. Items 2 through 5 are now sequenced as
F1-R1B carrier/admission, F1-R1C owner views/read closure, and F1-R1D
Relations/correspondence/package integration.

F1-I then replaces offline formed values with exact admitted live owner
handles, reissues the same views, checks source-authority bindings, and forms
the real Q1 question/result under an Analysis validation basis. If the live
owner cannot expose a required observation without trusting the exporter, the
owner-view boundary must be repaired. If the exact source lacks an observation
needed by the protected map, F0 reopens. Mere mismatch between this temporary
JSON identity and a later durable encoding is expected and is not itself a
semantic finding.

## 7. Effect on F0 and the main design

F1-R0 supports the F0 A/S/C composition and finds no reason to add a
`FormalKernel`, make a theorem prover authoritative, serialize live support,
change the Core/Protocol split, or rotate challenge/reduction ownership. It
does require the F1 entry sequence and minimum package contract to incorporate
the refinements above.

No durable target page should absorb this format or its local diagnostics yet.
The earliest durable change remains after exact F1-R1B/R1C/R1D and F1-I
evidence: owner portable-view contracts plus an Analysis formal-source
correspondence family.

## 8. Non-claims

- Neither checker is formally verified.
- Agreement between two programs does not prove the temporary contract sound
  or complete.
- Manual source bodies are not target canonical bodies and do not establish
  implementation correspondence.
- The evaluator does not construct a VCVio, ArkLib, SSProve, or EasyCrypt
  artifact.
- No theorem is selected, applied, transported, or proved here.
- No cryptographic, compiler, endpoint, or deployment claim follows.
