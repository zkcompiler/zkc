# K2 Protocol/Fiat--Shamir reference instrument

This bounded package exercises selected K2 Protocol/Fiat--Shamir contracts and
behavioral shapes. It is research evidence, not current zkc authority, a
compiler implementation, protocol conformance, or a cryptographic proof.

`reference_model.py` imports K1's canonical `Datum` and typed content-identity
machinery directly. It does not reproduce a second foundation. On top of that
fixed basis it implements a fixture-exact finite model with:

- three exact witness-local K1 language profiles: Interaction/Core+Fresh,
  Transcript/FS importing Interaction, and family-neutral public-view export
  importing only Interaction. They are exact preimages for this bounded
  evaluator, not the published target PIR profiles;
  every K2 semantic ID selects its exact profile in the preimage, and the
  selected root's exact one- or two-profile bundle is authenticated as an
  exact no-extra import closure. Issuance requires evaluator support only for
  that root and refuses a supported profile omitting any emitted subject kind;
- an exact finite total interaction schedule with explicit nested scope opens;
- first-class statements, public context and parameters, and optional
  verifier-private inputs;
- online prover generation through a prefix-only `ProverView`, separately from
  completed-record replay;
- Fresh challenge resolution through a runtime-only resolver invoked at the
  exact challenge occurrence, outside invocation data and identity;
- transitive dependency-derived public-coin eligibility over every represented
  public activity (`ProverMessage`, `VerifierMessage`, `Challenge`,
  `OraclePublish`, `OracleQuery`, `OracleAnswer`, `Check`, and `Terminal`), with
  private guards included and no authored `publicly_recomputable` escape hatch;
- refusal of authored `ProverMessage` dependencies, because that field is not
  present in the target Core carrier;
- exact whole-prefix comparison before every challenge draw, plus an exported
  required-influence ordered-subtrace audit view covering challenge conditions,
  reduction-required publications, and challenge draws;
- one fully specified fixture transcript initialization, framing, absorption,
  squeeze, state advance, bounded rejection-sampling, and typed-exhaustion
  behavior;
- a Core-scoped transcript-construction identity, with explicit Core,
  construction-self, and application-domain initialization headers;
- the same literal Core under Fresh and Fiat--Shamir challenge interpretations,
  while Fresh records carry no FS construction, transcript, or namespace;
- a standard finite native-oracle publication/query/answer extension;
- fixture-bounded reduction declarations, publication-to-challenge
  obligations, linear claim-consumer uses, a Last-Challenge falsifier, and
  terminal closure;
- checked Fresh/Fiat--Shamir structural correspondence.
- exact, owner-issued static-view projections for the five Core schemas, the
  Protocol-scoped execution schema, the three transcript-construction schemas,
  and the checked FS result schema, with canonical field manifests, explicit
  dependency closure, K1 owner-local source bindings, domain-profiled payload,
  no-policy/closure/requirement identities, typed consumer and purpose, and
  fresh exact-object guarded capabilities;
- a checked-FS authority boundary: the result view can be issued only from an
  affirmative same-Core/public-coin result, and forged or substituted checked
  authority is refused; and
- a separately identified public-setup invocation view containing only public
  context and public parameters. Statement values and the full invocation
  remain outside its body and inert portable K1 authority binding; its copied
  metadata cannot substitute for the exact live capability.

## Source-authority compiler dispatch

Every finite PIR source binding in this instrument now selects the producing
profile's four bound source compilers before forming a profiled semantic ID.
Interaction static views use arm 0 of the Interaction compiler;
canonical-framed static views and checked construction results use arms 0 and
1 of the canonical-framed compiler; and public-setup invocation views use arm
0 of the public-setup compiler. The payloads contain the owner-defined local
bodies, while requirement, no-policy, and policy-closure subjects contain the
owner-defined role and identity references. Consumer and purpose roles use the
common `(family, ContentRef(coordinate))` bodies.

This changes every finite authority identity derived from the former generic
six-field payload because the model now hashes the selected owner's tagged
equation. The tests reconstruct the canonical-framed execution payload from
its coordinate and ordered field-coordinate bodies, reject both the former
untagged record and an Interaction-family wrapper. A separate discriminator
compiles the current duplex owner profile from source, reconstructs its static
payload, rejects both predecessor shapes, and checks the two tagged arms of
every duplex source compiler.

The static-view manifest remains bounded to this package's finite field
catalog. Each represented field maps to one owner path and atomic boundary;
the instrument does not implement the durable recursive field resolver. The
checked-result payload uses the required six-field owner shape, but its
`checker_contract` coordinate is package-local because the owner page does not
define a content-ID constructor for that coordinate. Passing the gate therefore
does not establish target-wide checked-result authority correspondence.

Two narrow contract-vector families are target-exact rather than merely
fixture-shaped. They are built and admitted through K1 directly:

- `GuardOutcome` false and true bodies contain the exact K1 `MF` and `MT`
  Boolean datums, not a generic `MetaVariant`;
- `OracleAnswer` absent and present bodies carry the exact lookup-result sum
  `V(0, Unit) | V(1, element)`, admitted at the derived result type rather than
  at the bare element type.

Run the finite gate from the repository root:

```sh
python3 -B evaluation/k2-protocol-fiat-shamir/run.py --check
```

The tests include the two exact contract-vector families above, positive
Schnorr and native-oracle fixtures, and negative mutations for statement
binding, exact prefixes, duplicate or reversed influence, mandatory public
activity influence, challenge-condition framing, nontrivial guard framing,
private-guard public-coin failure, per-draw namespaces, transitive
dependency-sensitive public-coin eligibility, authored prover dependencies,
causal future reads, scope-local input visibility, sampling
retries/exhaustion, typed and scope-correct oracle indices, oracle lifecycle
and answers, extension refusal, schedule identity, nested-scope continuity,
grinding separation, claim linearity, reduction-required Last-Challenge
ordering, terminal closure, challenge-time Fresh resolution, resolver-free
Fresh replay, resolver-independent invocation identity, owner-view closure and
schema separation, Protocol-scoped execution views, checked FS view authority,
public-setup attenuation, profile-identity locality, and selected-profile
execution/replay identity. The focused runner owns the current discovered test
count.

## Evidence boundary

Passing the gate demonstrates only these finite executable cases. Except for
the two K1-backed contract-vector families identified above, the carrier and
execution results are fixture-exact or behavioral-shape evidence, not exact
Appendix-A conformance. The fixture predicates stand in for already admitted
K1 portable Bool algorithms; the instrument does not build `AlgorithmUse`, run
the K1 resolver/evaluator/evaluation-contract path, or provide a second general
evaluator. Its squeeze, advance, accept, and decode helpers likewise exercise
the selected behavior without claiming the durable algorithm ABI.

The model does not establish protocol soundness, Fiat--Shamir theorem
applicability, ROM/QROM security, extractor correctness, cryptographic
primitive correctness, complete IOP/PIOP/FRI coverage, unbounded recursion,
implementation conformance, or production readiness. Strategy generation
establishes causality only relative to a restricted Python API and the concrete
strategies exercised here; it does not implement a non-serializable causal
capability. Replay intentionally makes no strategy-existence claim.
The Fresh resolver is not supplied through `Invocation` or `ProverView`, and
the gate checks that it is first invoked at its challenge occurrence. Python
does not enforce process isolation or prevent a caller from deliberately
sharing ambient state between objects, so this is bounded API-order evidence,
not a universal noncommunication theorem for arbitrary host-language closures.

Public-coin eligibility is checked over this fixture's represented sinks and
dependency graph, not the durable model's complete `PCNode`/module graph. The
runtime does not represent verifier-only Oracle visibility; it uses
vector-indexed native oracles and exercises present answers. The exact
absent/present contract vectors demonstrate that both target answer bodies are
formable, not that the runtime executes sparse absent lookups.
Reduction applications are declarations anchored at schedule coordinates
rather than first-class executable reduction effects, and claim identifiers
carry no theorem semantics beyond the checked linear-use ledger.

The owner-view instrument is an exact contract witness for its finite field
catalog and closure rules. Its semantic IDs do execute K1's exact profile
preimage, selected-root no-extra import-closure, evaluator-support, and
supported-subject-kind machinery, but it does not yet execute the
durable view evaluator or generic field-path language. Its Python
capabilities model origin and object binding; they are not a host-language
security boundary. The public-setup view deliberately proves attenuation only:
it does not authorize execution, disclose Statement values, or replace the
separate Statement binding used by strong Fiat--Shamir.

The witness-local profile IDs are deliberately distinct from the published
target IDs in [`docs-next/pir/profiles/`](../../docs-next/pir/profiles/README.md).
The finite body encoders in this package are not the durable Appendix-A body
compilers, so substituting a target profile ID here would be a false semantic-
conformance claim. Joining those lanes requires an exact target body compiler
and admission evaluator, not an ID replacement.

This finite instrument also selects one challenge value per occurrence,
unconditional scope openings, one closing terminal, linear claims only, and
fixture-equivalent bounded predicates. It does not implement the durable
model's complete raw carrier and channel laws, joint draws, opaque oracle
bindings, guarded early terminals, reusable or shared claims, or complete
reduction semantics.
Its Schnorr control accepts according to the modular equation implemented by
this instrument; that equation is a positive behavioral control, not an
independently admitted K1 check algorithm or a proof of Schnorr soundness.
