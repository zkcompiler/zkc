# F0 Provisional Architecture, Rotation Cone, and F1/F2 Entry Contracts

> **Kind:** Temporary F0 convergence and dependent-program handoff
> **State:** Provisional F0 architecture selected for feasibility testing;
> F1-R1C0 has reopened F0-V at the owner-view schema/publication boundary;
> durable target repair remains unselected pending that design pass
> **Authority:** None. Placeholder schema names and implementation paths are
> research coordinates, not public contracts.

## 1. Provisional architecture

F0 provisionally selects this assurance topology for F1 falsification:

```text
existing admitted semantic owners
  -> owner-issued exact views and read manifests
  -> stable source authentication envelope
  -> question-relative semantic read projection
  -> checked source-package correspondence                 [Q1]
  -> provider-native formal artifact
  -> checked provider correspondence                       [Q2]
  -> theorem environment, truth, and applicability         [Q3--Q5]
  -> qualified property-specific Analysis judgment         [Q6]
  -> property-specific Compiler/OIR/Realization checks     [Q7--Q10]
```

Production of packages, provider terms, proofs, certificates, transform
targets, and endpoint artifacts is untrusted by default. Exact owners retain
semantic authority. Analysis owns formal-correspondence and property
propositions, validation bases, qualified results, trust closure, and reliance
capabilities. No theorem provider becomes a Protocol owner.

The architecture has two modes:

- **local mode:** exact live owner views feed a checker directly; useful before
  a portable product boundary or for confidential support; and
- **portable mode:** a stable neutral package carries canonical source
  authentication preimages and exact portable read projections for an
  independently released consumer.

The modes answer different deployment needs but check the same Q1 proposition
class. Portable bytes never carry live authority.

## 2. Package alternatives and selection

| Alternative | Benefit | Fatal or dominant problem | F0 disposition |
|---|---|---|---|
| live owner views only | smallest schema and no serialization duplication | independently released consumer cannot authenticate/replay without the zkc process; providers may choose divergent read sets | retain as local bootstrap, not portable architecture |
| full canonical owner bodies only | independent root-ID recomputation | provider can derive undocumented observations; no exact question-relative completeness/omission boundary | use only as authentication layer |
| read projections only | minimal and question-relative | asserted root IDs cannot be independently recomputed; projection authenticity depends on trusted producer or live owner | insufficient alone |
| full authentication preimages plus exact read projections | independent root authentication and explicit provider read closure | costs a stable schema, dependency closure, two decoders, and compatibility policy | **provisionally selected for portable mode** |
| universal formal AST | one apparent target for all proof systems | becomes a second semantic center and poorly fits VCVio, SSProve, EasyCrypt, and future frameworks | reject unless provider diversity proves impossible |
| certificate only | compact receiver input | certificate proposition/query cannot be reconstructed without authenticated source and observation semantics | evidence option only, layered on the selected package |

The selected package is not “the formal semantics.” It is a portable,
authenticated reading of existing semantics for one exact interpretation
contract. Provider-native formal terms remain separate.

## 3. Minimum temporary schema class

The following pseudostructures fix the F1 obligations without selecting durable
names or a wire encoding.

```text
FormalSourceContractCandidate = {
  semantic_regime_and_package_schema,
  root_owner_kinds_and_profiles,
  required_authentication_preimage_closure,
  portable_owner_view_coordinates,
  exact required read manifests and closure laws,
  protected observation catalog,
  excluded owner-local/confidential support catalog,
  source-to-projection totality and uniqueness law,
  finite decoding/checking controls,
  retention and compatibility policy
}

FormalSourcePackageCandidate = {
  contract_id,
  complete canonical root and dependency preimages,
  asserted root IDs recomputed from those preimages,
  exact owner-view coordinates and closed manifests,
  exact canonical projected entries,
  total source-to-package coordinate ledger
}

ProviderFormalArtifactCandidate = {
  source_package_id,
  provider_environment_id,
  provider_language_and_schema_id,
  exact provider-native artifact bytes and entry coordinates
}
```

The Q1 question binds the exact admitted owner roots, contract, package, and
equality/observation direction. The Q2 question binds the package, provider
artifact, provider-native observation semantics, total maps, and assumptions.
Validation bases name the decoders, package checker, provider adapter/checker,
finite controls, proof environment, and residual trust.

Q1 checking must reconstruct root IDs, every required-read fixed point, exact
entry equality, and the complete coordinate ledger. Q2 checking must preserve
typed occurrence identity, order, visibility, challenge correlation,
transcript interpretation, Oracle mode/state, claims/reductions, terminals,
failures, relation roles, and every observation selected by the contract.

The portable contract may name role/type declarations for witness, Plan, or
Oracle-private material, but its excluded-support catalog prevents live secret
values, mutable state, and causal capabilities from entering the package. A
separate owner-local support binding supplies them only to an authorized local
question.

## 4. Proposed ownership if F1 succeeds

| Concern | Proposed durable owner | Reason |
|---|---|---|
| semantic root and view schema | existing PIR, Interface, Plan, Relations, Analysis, Compiler, or OIR owner | source meaning and read closure remain local to the domain |
| generic canonical envelope/ID primitives | Foundation only if existing primitives are insufficient | Foundation may own representation mechanics, never formal-domain meaning |
| formal source contract, package Q1 proposition/result, provider Q2 proposition/result | Analysis family with exact foreign-owner source bindings | these are validation and reliance questions over several owners, not a new source domain |
| stable package wire schema and compatibility window | the formal-extraction/independent-consumer boundary, routed from project architecture | serialization exists because of a named consumer and retention promise |
| provider environment and theorem validation | Analysis validation basis and theorem-source validation | proof-system trust is validation metadata, not Protocol identity |
| package/provider exporters | untrusted tooling | production does not mint semantic authority |
| property-preserving transition | exact relation owner plus Analysis property transport; Compiler orchestrates/consumes | transition meaning and property truth remain separate |
| endpoint realization | OIR/Realization after activation | formal Protocol proof stops before endpoint implementation |

This assignment deliberately avoids `FormalKernel`, `ProofAuthority`, or a
theorem-prover-owned top-level subject.

## 5. Target changes and explicit non-changes

### 5.1 F1-driven changes

F1 evidence now requires item 1 before R1C can resume. Later affirmative F1
evidence may justify items 2--7:

1. repairing the PIR owner-view publication contract with a closed schema
   catalog, exact nested body grammars, law bindings, closure dispatch, and
   authority-envelope bodies before owner-view evaluation proceeds;
2. selecting the formal-extraction trigger and its retention/compatibility
   promise in `docs-next/project/protocol-ir-architecture.md`;
3. specifying portable owner authentication preimages and package read
   projections without altering owner subject identity;
4. instantiating a formal-source/provider-correspondence family in Analysis;
5. defining package/checker/translation contracts, validation bases, exact
   outcomes, cold replay, and reliance policy;
6. adding two independent package decoders/checkers and mutation vectors; and
7. defining one property-specific transition family for the first Compiler
   preservation pilot.

### 5.2 Surviving non-changes and the reopened claim

F0 finds no current reason to change:

- `InteractiveCore` fields or occurrence order;
- the `CoreId`/`ProtocolId` split or profile-sensitive challenge
  interpretation;
- challenge correlation and reduction-sharing declarations;
- owner ownership of static views and nonserializable causal capabilities,
  although their exact publication and issuance schema now requires repair;
- Relations ownership of definitions, satisfaction, refinement, and
  correspondence;
- Analysis ownership of properties, theorem applicability, trust closure, and
  property transport;
- Compiler's separation of proposal, PIR admission, transition qualification,
  assessment, and decision; or
- OIR/Realization activation order.

The A/S/C topology therefore survives, but the former positive claim that the
existing owner-view contract was already exact enough does not. F1-R1C0 found
that the authenticated Interaction source names the required facts while the
published profile omits the promised closed schema catalog and exact
machine-resolvable bodies. F0-V must repair that owner boundary; Analysis must
not compensate by inventing a second schema.

## 6. Rotation cone

| Layer | F0 impact | Earliest durable change if F1 succeeds | Must not be inferred |
|---|---|---|---|
| current `docs/` and current C++ semantics | none; current receipt limitation is documented | later roadmap/status update only after a real bridge lands | target design is implemented now |
| `docs-next/project/` | records formal-extraction trigger and integrated owner boundary | after F1 validates package class and consumer | package bytes or public compatibility are selected by this note |
| `docs-next/pir/` and family transcript pages | F0-V must repair the owner-view schema, field/law resolution, and authority-envelope publication contract | before F1-R1C resumes, after explicit migration review | formal provider syntax enters Protocol identity |
| `docs-next/relations/` | may need portable relation source projection hooks if generic owner views are insufficient | only after Schnorr relation package test | relation satisfaction becomes Analysis-owned |
| `docs-next/analysis/` | main semantic addition: Q1/Q2 family and validation/reliance rules | after F1 proposition/result behavior is falsified | a universal proof language or one assurance Boolean |
| `docs-next/compiler/` | one property-specific transition consumer/validator | F2 or later pass pilot | generic target admission preserves properties |
| `docs-next/oir/` and Realization | no F1 change | later target-specific Q9/Q10 pilot | Protocol proof reaches deployment |
| Foundation | likely no semantic change; perhaps generic package encoding primitives | only if existing canonical body/ID machinery cannot express the envelope | formal assurance becomes a Foundation domain |
| implementation and evaluation | disposable exporter/checkers, vectors, provider model | F1/F2 only, clearly marked non-authoritative | prototype defines target semantics |

The likely durable cone is therefore additive and concentrated in project
architecture, owner portable-view contracts, and Analysis. Candidate R would
rotate every row and is not justified by the observed capability gain.

## 7. F1 exact entry contract

F1 is split so research can proceed before the semantic redesign is fully
implemented.

### 7.1 F1-R — reference package and checker feasibility

**Source subject.** One bounded Fresh Schnorr verifier subject represented by
the selected target's exact canonical bodies:

- admitted `InteractiveCore` and Fresh `Protocol`;
- public statement binding;
- message/challenge/response/check/terminal occurrences;
- exact `PublicBindingView`, `StrategyDecisionView`, `PublicCoinView`,
  `EffectView`, `ClaimReductionView`, and Protocol `ExecutionView` closures;
  and
- exact relation definition/model/instance roles and Protocol correspondence
  needed to state the verifier relation.

No `ProverPlan` or live witness value enters the positive portable package.
An optional local-only extension may later test an honest-strategy proposition.

**Contract.** The temporary two-layer schema in Section 3, with whole static
Protocol/relation authentication preimages and a question-relative verifier-
and-relation observation projection.

**Producer.** An explicitly untrusted exporter. The producer may use any
convenient implementation and its output carries no result authority.

**Independent checkers.** Two implementations with no shared package parser or
canonical encoder. The first practical pair should be zero-dependency Python
and Rust, because both toolchains already exist in the repository ecosystem.
Neither checker may call the exporter or accept asserted root/package IDs.

**Positive result.** Both checkers independently recompute identical root and
package IDs, exact manifests, and one Affirmative Q1-style result over the same
formed proposition.

**Required negative mutations.** At minimum:

1. alter one canonical root preimage while retaining its asserted ID;
2. omit one producer/type/order dependency from a manifest;
3. add one phantom provider read;
4. alias two equal-typed occurrence coordinates;
5. duplicate one shared-challenge discriminator into two equal values;
6. reorder two interleaved occurrences;
7. replay the package under a different challenge interpretation/profile;
8. omit one FS transcript input in the reserved FS mutation fixture; and
9. attempt to serialize an owner-local confidential value or causal
   capability coordinate.

Each mutation must have an exact expected Negative, Refused, KindMismatch,
Malformed, or noncompletion class. “Any failure” is insufficient.

**F1-R success claim.** Only that the package class and independent checking
boundary can express and discriminate the bounded Q1 proposition. It does not
establish checker soundness, provider correspondence, theorem truth, security,
or implementation conformance.

### 7.2 F1-I — live owner integration

F1-I waits only for the relevant target owner-view and canonical-body
implementation, not for all semantic redesign work. It replaces manually
formed source inputs with live admitted owner handles, reissues exact views,
and demonstrates equality with the F1-R package/checker results.

If F1-R discovers a missing source fact, F0 reopens immediately. If F1-R
succeeds but F1-I cannot bind the live owner views without trusting the
exporter, the implementation boundary—not the package bytes—must be repaired.

### 7.3 Execution refinement after the first F1 pass

The first executable pass found that this entry contract joined two distinct
premises. The package/checker boundary can be tested over manual target-shaped
values, but the live K2/K3 evaluators explicitly do not supply the durable
target body compilers or target profile identities required by the “exact
canonical bodies” premise above. F1 is therefore refined without changing the
selected topology:

```text
F1-R0  manual package/checker and mutation feasibility
F1-R1A exact target profile/source basis and fixture discriminator
F1-R1B exact target carrier and admission
F1-R1C0 owner-view source determinacy
F0-V    owner-view schema/publication repair
F1-R1C  exact owner views and read closure
F1-R1D exact Relations/correspondence/package integration
F1-I   admitted live-owner issuance and authority binding
```

The bounded F1-R0 result and exact nonclaims are recorded in
[`f1r-reference-package-feasibility.md`](f1r-reference-package-feasibility.md).
F1-R0 cannot satisfy Q1 or mint an Analysis capability. The bounded F1-R1A
result now closes only the independently published target profile/source
basis and mechanically refuses fixture or identity-only substitution. The
subsequent bounded F1-R1B result forms and admits one complete fourteen-field
target slice and requires that exact admitted handle for Fresh Protocol
formation; it remains offline research authority and explicitly fails closed
outside the selected constructor fragment. F1-R1C0 then returns
`CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`: the six view surfaces are
authenticated, but an independent evaluator cannot resolve the promised exact
schema and read closure without making owner choices. F0-V is therefore open,
R1C waits on its publication repair, and R1D/F1-I retain the package and live
source-authority obligations in Sections 7.1 and 7.2. The split prevents
profile publication, fixture-local bodies, or an offline admitted record from
being mislabeled as live target correspondence.

## 8. F2 exact entry contract

F2 begins only with one affirmative F1 Q1 result and retains three stages.

### 8.1 F2-O — operational correspondence

- pin one exact VCVio revision and full Lean/dependency/toolchain environment;
- derive one `OracleComp`-based provider artifact from the F1 package;
- define a typed step/trace relation preserving occurrence identity/order,
  messages, challenges, Oracle actions, checks, terminals, and qualified
  failure;
- use an untrusted generator and independently check Q2 correspondence; and
- include both honest completion and every supported failure/noncompletion
  branch in the stated relation.

F2-O establishes no cryptographic property.

### 8.2 F2-P — one property path

**Selected provider declaration.** The first property path uses
`Schnorr.sigma_complete` from
`Examples/Schnorr/SigmaProtocol.lean` at VCVio revision
`de0a3108140e3e04a7ebf0075aa110b459ee6e8a`. Its elaborated assumptions are:

- `F : Type`, `Field F`, and `SampleableType F`;
- `G : Type`, `AddCommGroup G`, `Module F G`, `SampleableType G`, and
  `DecidableEq G`; and
- one `g : G`.

Its conclusion is `(Schnorr.sigma F G g).PerfectlyComplete`. Unfolding that
provider proposition gives the exact quantitative claim: for every valid
statement/witness pair, the honest commit, uniform challenge, response, and
verification computation accepts with probability exactly `1`. The theorem
does not require a generator or scalar-to-group bijection hypothesis.

**Validation basis.** At that revision, Lean `v4.33.1` with the pinned Lake
manifest successfully built `Examples.Schnorr.SigmaProtocol`. A direct
declaration probe succeeded, and `#print axioms` reported `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` in the reported
closure. This is a bounded Q3/Q4 input, not Q5 applicability.

**Target proposition.** F2-P asks whether the exact F1 Fresh Schnorr subject,
under an exact Q2 correspondence to `Schnorr.sigma F G g`, has perfect honest-
verifier completeness with acceptance probability `1`. Q5 must bind the
statement, witness, relation, commit, challenge, response, verifier, uniform-
sampling, and probability interpretations—not theorem names or shape alone.
The resulting Q6 judgment must retain the typeclass assumptions, provider
environment, standard Lean axiom closure, Q1/Q2 support, and any residual
adapter/checker trust.

F2-P must separately form Q3 environment authentication, Q4 theorem truth
treatment, Q5 applicability, and Q6 target property. If the exact theorem is
present but the source/provider map or a required semantic premise cannot be
established, the successful result is a precise `CannotAnswer` or assumption-
bearing judgment plus the closed Q1/Q2 evidence, not a weaker property
relabeled as success. A missing named pinned dependency is instead
`MissingDependency`.

### 8.3 F2-D — zkc-native discriminator

The architecture cannot be accepted on alternating Schnorr alone. F2-D must
run at least one of:

- the interleaved two-reduction/one-shared-challenge case;
- canonical Fiat--Shamir with exact transcript influence and typed sampling
  failure; or
- another schedule whose semantics a strict sequential model would erase.

The leading choice is the shared-challenge case for structural discrimination,
followed by the FS transcript-omission mutation because it is security-
motivated. ArkLib may be used only if an exact adapter forms; direct VCVio is
the default comparison, not an assumed winner.

## 9. Execution and worktree strategy

F0, F1-R, and sequential F1-I work should continue on the current shared
design branch with committed checkpoints. This lets each phase inspect the
exact prior package and prevents unexplained dirty handoffs.

Use separate worktrees only when work is genuinely concurrent or needs
incompatible build states—for example, one worktree integrating the package
checker while another pins/builds a large Lean/VCVio environment. External
formal checkouts and generated proof/build artifacts remain outside the zkc
repository unless a reviewed pinned integration explicitly requires source or
small conformance vectors.

There is no need to wait for the entire semantic redesign before F1-R. Its job
is to falsify the written source/package boundary and may influence the design.
F1-I and any production claim do wait for the relevant admitted owner-view
implementation. This preserves feedback into the redesign without pretending
that a reference fixture is the implementation.

## 10. F0 closure status

The first F0 architecture pass now supplies all nine charter outputs at
research resolution:

1. current and target code/spec reconstruction;
2. primary-source/framework ledger;
3. owner/identity/lifecycle/consumer map;
4. assurance lattice and trust map;
5. equal-resolution candidate matrix;
6. scenario/counterexample results;
7. provisional architecture and reversal conditions;
8. gap and rotation-cone analysis; and
9. exact staged F1/F2 entry contracts.

F0 remains reopenable throughout F1/F2. F1-R1C0 has now exercised that rule:
the broad architecture pass is complete, while the narrow F0-V owner-view
publication repair is open. “Closed” here never meant normative design freeze.

## 11. Non-claims

This handoff does not select a wire format, promise public compatibility,
authorize implementation outside the research lane, prove either checker,
establish any provider theorem as applicable to zkc, or change roadmap
priority. F1/F2 results must return to the durable owners before any target or
current claim changes.
