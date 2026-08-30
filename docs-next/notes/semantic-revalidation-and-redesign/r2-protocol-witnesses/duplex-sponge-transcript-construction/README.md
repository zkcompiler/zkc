# Duplex-Sponge Transcript Construction

> **Kind:** Temporary semantic research-package charter and inventory
> **State:** Complete; the sibling-profile candidate is selected, durably
> promoted, executable gates pass, and bounded independent closure review found
> no release blocker
> **Authority:** None. This package may falsify or motivate a target change,
> but it cannot define PIR semantics, establish theorem applicability, claim a
> secure sponge instantiation, or report implementation support.
> **Entry baseline:** At package entry, the active target admitted one canonical-framed
> transcript construction. Prior cross-protocol research found that the
> source operational duplex-sponge transform does not fit that construction's fixed
> initialization, proof-material, framing, namespace, or retry envelope.
> **Intended destinations:** Accepted construction and execution semantics go
> to their exact owners under `pir/`; theorem-premise projections and
> nonclaims go to `analysis/`; integrated rationale and support boundaries go
> to `project/`; a retained finite falsifier remains under `evaluation/` only
> if its exact claim survives convergence.
> **Deletion trigger:** Delete this package after every accepted definition,
> rejection rationale, source caveat, nonclaim, implementation gap, and
> deferred question has a durable owner and no durable page depends on this
> directory.

## 1. Central question

Can zkc represent the source construction in Chiesa and Orrù's
*A Fiat--Shamir Transformation From Duplex Sponges* as one independently
identified transcript construction over an unchanged public-coin
`InteractiveCore`, while:

- preserving exact Statement-binding and prover-message occurrence/evaluation
  coverage while leaving encoder injectivity to correspondence and Analysis;
- keeping proof-carried construction material outside the source Core;
- leaving the canonical-framed construction unchanged;
- separating construction execution from ideal-model and theorem premises;
- giving construction-material preparation, verification, and replay explicit
  authority while routing honest salt generation to Plan/Realization;
- making future construction-family evolution visible without an opaque
  callback or caller-authored success boundary; and
- retaining one exact same-Core Fresh/Fiat--Shamir structural judgment?

The package may select a conservative extension, an intentional v0 boundary,
or a wider redesign if exact identity, execution, or consumer pressure makes a
local construction incoherent. The prior extension sketch is input, not the
default winner.

## 2. Scope and non-goals

### In scope

- the exact operational state and transition laws of the reviewed source;
- statement-to-runtime-instance correspondence required by zkc;
- construction-owned public proof material and its generation/replay paths;
- prover-message codecs, challenge decoders, round coverage, and final-round
  prover/verifier asymmetry;
- construction identity, profiles or modules, admission, refusal, execution,
  receipts, replay, and same-Core checking;
- the minimum common influence law shared with the canonical-framed
  construction;
- exact PIR-owned source views required by Analysis and endpoint projection;
- evolution locality when a later transcript-construction family is added;
- a finite executable state-transition and schedule falsifier; and
- the current-to-target implementation and migration gap.

### Out of scope

- proving the source paper's soundness, knowledge-soundness, or zero-knowledge
  theorems;
- claiming that a concrete permutation, hash, sponge, or implementation
  realizes an ideal oracle model;
- selecting a production ciphersuite or concrete proof-byte format;
- activating QROM, UC, state-restoration, or duplex security Analysis
  families;
- weakening the canonical-framed construction to mimic another transform;
- adding salt, domain headers, or transformed challenges to the source Core;
- a universal transcript programming language or arbitrary event callback;
- full endpoint, realization, deployment, or evidence-policy design; and
- implementation compatibility as a semantic selection constraint.

## 3. Frozen source and comparison set

The source-of-record is the 27 March 2026 revision of Chiesa and Orrù,
[ePrint 2025/536](https://eprint.iacr.org/2025/536), reviewed PDF SHA-256
`fca7ba09ebe59141c3c041ac660b4e3e161fdab8a709aee67e236db8d8da3a35`.
Construction 3.3 owns the operational duplex state machine; Definitions
4.1--4.2 and Construction 4.3 own the codec, ideal-oracle, and transform
shapes. Theorems and proof prose may contribute Analysis requirements but do
not override the operational pseudocode.

The 17 August 2026
[CFRG Fiat--Shamir draft 03](https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.html)
is a work-in-progress operational comparison, not source authority for the
paper construction. The reviewed text SHA-256 is
`4ed563b26f3e366545e280a979d46b6ce623e27a29b53b73fa7cb92c5287fc28`.
Its session identifiers, serialization, strict parsing, codecs, and test
vectors pressure Interface and OIR choices; its duplex/XOF behavior must not be
silently equated with Construction 3.3.

Official Keccak duplex material, STROBE, and Merlin may contribute comparison
lessons about state, framing, domain separation, and protocol transcripts.
They cannot establish correspondence to the source construction or ratify a
zkc abstraction.

## 4. Required research lenses

### Reconstructive

1. Recover the exact source state, indices, transition order, salt position,
   message schedule, proof tuple, and final-round behavior.
2. Reconstruct the current Foundation, Core, transcript-construction,
   invocation, record, Analysis-view, Interface, and OIR boundaries.
3. Identify every implementation surface that would need to move, without
   allowing current code to define the target.

### Generative

4. Compare at least these candidates at equal resolution:
   - retain the current construction and make duplex support an explicit v0
     boundary;
   - overload or parameterize the canonical-framed construction;
   - add a closed construction alternative under one shared profile;
   - separate common Fiat--Shamir semantics from construction-specific
     profiles or authenticated construction modules; and
   - use a generic finite transcript transducer with independently enforced
     coverage laws.
5. Ask whether a clean-room design can add a later construction family without
   rotating unrelated existing subjects or accepting an opaque callback.
6. Identify useful capabilities beyond the reviewed paper, but keep them out
   of the selected kernel unless at least two materially different consumers
   need one common law.

### Evaluative and integrative

7. Compare semantic clarity, authority, identity, source fidelity,
   compositionality, independent implementability, evolution, theorem
   separation, and cost.
8. Pressure every viable candidate with source-faithful operational traces and
   well-formed negative mutations.
9. Reconcile the selection with Core execution, Analysis source views,
   endpoint parsing, canonical identity, and existing canonical-framed
   witnesses.

## 5. Source facts that must not be assumed away

The package begins with the following propositions as recheck obligations,
not yet as selected zkc semantics:

- `Start_h(x)` derives capacity state from the runtime instance and starts
  with absorbing index zero and squeezing index equal to the rate;
- absorption is overwrite-mode, resets the squeezing index even for empty
  input, and applies the permutation only when another symbol reaches a full
  rate segment;
- zero-length squeeze is an exact no-op, while a positive squeeze resets the
  absorbing index and continues one mutable output stream;
- one uniformly sampled salt is absorbed before every prover message and is
  carried in the argument string;
- each round uses one fixed-length injective prover-message codec and one total
  challenge decoder over a fixed squeeze length;
- the argument contains salt and prover messages, not verifier challenges;
- the prover need not execute the final squeeze, while the verifier does;
- the paper codec does not define zkc's statement-to-bitstring
  correspondence;
- theorem proofs may require inverse-sampling, alphabet, and resource premises
  stronger or more precise than the construction definition states; and
- ideal random-function/permutation access, including inverse-permutation
  access, is an Analysis experiment premise rather than execution semantics.

Any conflict between pseudocode, cost prose, theorem proof, draft behavior,
or a local implementation is recorded rather than normalized silently.

## 6. Executable evidence contract

The finite executable package is a transition and admission falsifier, not a
cryptographic implementation. It must:

- use a small frozen alphabet, rate, capacity, runtime instance, and bijective
  toy permutation;
- state that the toy hash and permutation establish no security property;
- derive expected states from an independent literal model rather than copy
  target outputs into fixtures;
- cover initialization, empty and nonempty absorption, exact rate-boundary
  behavior, zero and consecutive squeezes, absorb-after-squeeze, and
  squeeze-after-absorb;
- cover one complete multi-round proof schedule with salt, all prover
  messages, all verifier challenges, and final-round asymmetry;
- reject XOR absorption, eager permutation, empty-absorb no-op, prefix-XOF
  substitution, missing or misplaced salt, missing or duplicated message
  coverage, wrong codec length, wrong decoder, wrong challenge order, and
  construction-identity substitution;
- distinguish structural replay from uniform salt generation, ideal-model
  realization, and theorem applicability; and
- rerun the affected canonical-framed Fresh/Fiat--Shamir cases without
  weakening their statement, message, prefix, namespace, or retry laws.

Executable promotion is justified here because several transition differences
are observationally subtle and prose-equivalent implementations can disagree
at empty-input, partial-squeeze, and rate-boundary cases.

## 7. Package outputs and inventory

This README owns every direct child of this directory. The compact output set
is:

| Page | Role |
|---|---|
| `source-and-current-model.md` | Exact source ledger, source caveats, current semantic and implementation reconstruction, comparison systems, and owner map. |
| `design-space-and-selection.md` | Equal-resolution candidates, opportunity analysis, identity/evolution decision, selected target, counterexamples, and reversal conditions. |
| `executable-validation.md` | Frozen finite model, independent oracle, mutations, replay commands, claim boundaries, and results. |
| `convergence-and-promotion.md` | Cross-owner reconciliation, durable changes, implementation gap, absorption map, residual work, and closure review. |

The executable directory, if retained, must have its own README, source ledger,
frozen inputs, tests, deterministic report contract, and exact nonclaims. It
must not import target-document data structures as its oracle.

## 8. Exit gate

The package closes only when:

1. the exact source construction and every discovered source ambiguity are
   reconstructible from pinned primary sources;
2. the selected candidate defines one exact construction subject, authority,
   identity, lifecycle, runtime input, transition, receipt, refusal, replay,
   and source-view contract;
3. Statement-binding and prover-message occurrence/evaluation coverage cannot
   be weakened by an authored skip map or positive witness shape, while codec
   injectivity remains an explicit separate premise;
4. construction execution, generation provenance, ideal-model assumptions,
   theorem applicability, proof serialization, and implementation evidence
   remain separate judgments;
5. the finite executable package distinguishes every material transition and
   schedule candidate and reruns affected canonical-framed boundaries;
6. all accepted changes are promoted to their exact durable owners with no
   durable dependency on this package;
7. the current-to-target implementation gap and migration order are explicit;
8. one independent bounded review finds no unresolved source, identity,
   authority, or architecture blocker; and
9. the closure record states whether the original objective succeeded, the
   exact result, any portfolio reordering, and the next package contract.

Passing this gate establishes no cryptographic theorem, secure instantiation,
production implementation, protocol-family support, semantic freeze, or
normative cutover.
