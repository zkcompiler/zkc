# F0 Primary-Source Ledger

> **Kind:** Temporary primary-source and framework ledger
> **State:** Initial live-source pass complete for VCVio and ArkLib; broader
> formal-method and compiler-validation sources pending
> **Authority:** None. Source inspection informs candidates; it does not prove
> zkc correspondence, theorem applicability, build success, or axiom freedom.
> **Observed:** 2026-09-02

## 1. Snapshot ledger

| Source | Inspected revision | Role in F0 | Limit of use |
|---|---|---|---|
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | `de0a3108140e3e04a7ebf0075aa110b459ee6e8a`, 2026-09-01 | Candidate foundation for typed oracle computations, denotational probability, handlers/simulation, game reasoning, RBR, Fiat--Shamir, interaction, and implementation correspondence | No zkc encoding, subject correspondence, or zkc property theorem was found or claimed; checkout was inspected but not built in this pass |
| [ArkLib](https://github.com/Verified-zkEVM/ArkLib) current main | `9cf545c02a461ac7dbe6e522b3fb7bd803d35d89`, 2026-09-01 | Candidate higher-level IOR/reduction, composition, protocol, and proof-system theorem provider | Current source is not the revision authenticated by zkc receipts; source inspection does not establish theorem completeness or axiom freedom |
| ArkLib revision pinned by zkc | `fad5cbf808774838924dc8273715724c6a6caa1f`, 2026-07-25 | Exact source of current zkc ArkLib receipt and surveyed-absence claims | Intentionally historical; it cannot be used to report current ArkLib-main capability |
| ArkLib's current VCVio dependency | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` | Shows the actual foundation beneath current ArkLib `OracleComp`, probability, simulation, and related infrastructure | Dependency does not make ArkLib and VCVio theorem interfaces identical or make ArkLib theorems applicable to zkc |

The current ArkLib main inspected here is 93 commits beyond the zkc pin. A
scoped source diff over `OracleReduction`, `ProofSystem`, `README.md`, and the
Lake configuration reports substantial change, including new and revised RBR,
composition, transcript-tree, protocol-component, FRI, Sumcheck, Binius, STIR,
and toy-problem material. This is a refresh trigger, not evidence that a
previously missing zkc obligation is now closed.

## 2. VCVio source observations

### 2.1 Computation subject

**Observed:** `OracleComp spec α` is a free monad over an indexed
`OracleSpec`. Its canonical cases are pure return and one oracle query followed
by a response-indexed continuation. `OptionT (OracleComp spec)` supplies an
explicit failure layer.

**F0 use:** This is a plausible semantic target for an ordered zkc interaction
runner because interaction is represented as computation rather than as fields
on one universal protocol record.

**Limit:** A free oracle-computation tree does not by itself carry zkc's
Protocol, relation, occurrence, identity, visibility, challenge-prefix,
reduction-group, terminal, or owner-authority meaning. An interpretation and a
checked correspondence remain necessary.

### 2.2 Interpretation and handlers

**Observed:** `simulateQ` replaces each oracle query with a supplied
`QueryImpl` in a target monad. Current VCVio contains logging, caching,
pre-generation, query bounds and costs, programming, tracing, random-oracle,
and operational/coinductive interaction support.

**F0 use:** This supports the hypothesis that transcript execution, random
oracle interpretation, logging/caching correspondence, resource observation,
and later implementation semantics can be separate handlers over one zkc-
derived computation.

**Limit:** Handler composability in VCVio does not prove that a handler order
or state split matches zkc's event order, absorb/squeeze discipline, failure
precedence, or shared state.

### 2.3 Probability and program logic

**Observed:** VCVio exposes measure-valued and finite-subprobability semantics,
output/event/failure probabilities, unary Hoare-style reasoning, relational
coupling-style reasoning, and game-transform tactics. The current tree also
contains round-by-round, Sigma-protocol, Fiat--Shamir, forking/rewinding,
asymptotic, cost, and interactive-system modules.

**F0 use:** VCVio is now a materially stronger F2 candidate than the older
local ecosystem summary alone demonstrated. It can potentially host both
operational correspondence and property-specific game reasoning.

**Limit:** The current generic RBR layer documents a strictly alternating
message/challenge model, with padding for absent sides. Whether that faithfully
represents arbitrary zkc schedules, interleaving, joint challenges, and
multi-effect reductions is a required F2 discriminator, not an assumption.

## 3. ArkLib source observations

### 3.1 ArkLib is layered on VCVio

**Observed:** Current ArkLib's Lake configuration directly requires VCVio.
`OracleReduction` imports VCVio oracle-computation and simulation modules, and
several compatibility files record functionality moving upstream to VCVio.

**Consequence:** F0 should not frame the design as choosing unrelated theorem
foundations. The more accurate candidate topology is:

```text
VCVio generic oracle/probability/game substrate
  -> ArkLib higher-level IOR/proof-system abstractions and theorems
  -> optional exact adapter for a matching zkc subject
```

zkc may still use VCVio directly when its native subject does not fit ArkLib's
higher-level ontology.

### 3.2 High-level protocol and reduction shape

**Observed:** `ProtocolSpec n` is an indexed finite sequence of prover-to-
verifier or verifier-to-prover steps and associated types. `OracleReduction`
adds input/output statements, witnesses, oracle statements, prover/verifier
algorithms, execution, relations, and security notions. Sequential composition
has substantial definitions and theorem surfaces.

**F0 use:** ArkLib remains a strong selective provider for standard IOR and
sequential-reduction subjects and a useful comparison model for the minimum
information a zkc formal view must preserve.

**Limit:** zkc's structural reduction also binds claim-flow, owner occurrences,
event subsets, transcript influence, interleaving, shared challenges, checks,
terminal routes, and exact source views. Shape similarity cannot establish
that one ArkLib `OracleReduction` denotes the same subject.

### 3.3 Current open boundaries material to zkc

**Observed:** At the inspected current main:

- `OracleReduction/Composition/Parallel/Basic.lean` remains an explicit TODO
  surface rather than a general parallel-composition theorem library;
- the basic Fiat--Shamir file defines the transformation and a completeness
  theorem with an open proof, while state-restoration-to-Fiat--Shamir
  soundness remains a TODO in that file; and
- comments in the current reduction layer still describe active prover-model
  refactoring and distinctions among soundness, knowledge soundness, honest
  prover input/output, and adversarial interaction.

**Consequence:** Direct VCVio modeling is not merely a fallback for an old
ArkLib snapshot. It remains a credible route for zkc-native parallel,
interleaved, shared-challenge, transcript-runner, and Fiat--Shamir questions.

**Limit:** These source observations are file-local. They do not assert that no
other ArkLib module proves a related theorem, and they do not replace an
axiom-sweep or exact theorem-demand audit.

## 4. Initial architecture implications

### I1 — generalize the provider model

F0 should compare a provider-neutral Analysis validation basis with both:

- direct VCVio operational/property proofs; and
- ArkLib declarations whose formal subjects have an exact checked adapter.

The provider identity must include the formal environment and trust profile,
but it must not enter the intrinsic identity of the zkc Protocol.

### I2 — split generic operational correspondence from theorem-library adaptation

A reusable zkc-to-VCVio interpretation may establish runner, trace, handler,
and probabilistic meaning. A separate, partial zkc-to-ArkLib adapter may reuse
high-level theorems. One adapter's success must not be required for the other,
and neither may silently widen the property claim.

### I3 — refresh is separate from bridge progress

The current ArkLib pin predates substantial upstream work. F0 must eventually
refresh the theorem-demand inventory against current main or a new reviewed
pin. Moving the pin, reproducing more declarations, or observing fewer
`sorryAx` dependencies is provenance progress only until exact zkc subject
correspondence and consumer admission are checked.

### I4 — the F2 discriminator must exceed strict alternation

The first VCVio pilot may use a simple alternating Schnorr or sequential
reduction. F2 cannot select the architecture on that case alone. It must also
test one zkc-native schedule with interleaving, shared challenge, explicit
terminal/failure meaning, or another observation that a simple alternating
model could erase.

## 5. Pending primary-source work

F0 still requires:

- exact VCVio theorem and trust surfaces for the selected F2 cases;
- an ArkLib current-main axiom/theorem-demand refresh without changing the zkc
  pin prematurely;
- Lean kernel and proof-environment identity/trust references;
- proof-carrying code and proof-producing compilation;
- translation validation and refinement proof methodology;
- hax or another extraction path and its stated trust/correspondence limits;
- CompCert-style whole-compiler verification as the high-cost comparator; and
- at least one independent cryptographic proof framework, such as SSProve or
  EasyCrypt, to ensure the provider-neutral contract is not Lean-specific by
  construction.

## 6. Non-claims

No external checkout was built in this pass. No Lean declaration was checked,
no axiom sweep was run, no zkc-to-VCVio or zkc-to-ArkLib mapping was
implemented, and no current ArkLib theorem was admitted by zkc. Revision and
source-shape observations are research evidence only.
