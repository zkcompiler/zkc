# F0-V2B2C1B4 Module Owner Projections

> **Kind:** Temporary reopened-F0 constructor-isolation research result
> **State:** Complete for three semantic-module B2C families at bounded
> research resolution with
> `Affirmative/F0V2B2C1B4-A-MODULE-OWNER-PROJECTIONS`; one B2C family and both
> B2D integration families remain open
> **Authority:** None. This note and executable package do not change PIR, the
> Interaction profile, semantic-module identity, evaluator support, compiler,
> runtime, formal theorem, or Analysis judgment
> **Predecessor:**
> [`F0-V2B2C1B3 Claim and Reduction owner projections`](f0v2b2c1b3-claim-reduction-owner-projections.md)
> **Executable gate:**
> [`evaluation/formal-source-module-owner-projections-f0v2b2c1b4`](../../../../evaluation/formal-source-module-owner-projections-f0v2b2c1b4/README.md)

## 1. Decision

The existing owner topology can represent `NoProverDecision`,
`ProverDecision`, and `ProverPublication` module effects without adding a
module-specific kernel, transcript root, or semantic token. The selected
shape is:

```text
exact canonical Core bytes
  + exact authenticated used-module preimage closure
  -> strict owner-local module admission
  -> immutable admitted Core snapshot
  -> module declarations determine decision/output/control semantics
  -> Core occurrence coordinates determine uses and graph placement
  -> five Core-owned normalized views

same Core + exact Fresh Protocol bytes
  -> same-evaluator Fresh pairing
  -> Protocol-owned ExecutionView

same subject/source bytes + exact references
  -> separate cold parser and graph/projector
  -> independently derived six view bodies
```

The semantic module owns its local declaration meaning. The Core owns the
selected module/declaration coordinate, payload references, occurrence guard,
and schedule position. The evaluator support fingerprint owns the exact set
of module bodies and declarations it implements. No downstream view may
replace these owners with a caller-asserted decision class or visibility bit.

## 2. Executable scope and result

The fixture module has three exact `pir.core-effect` declarations:

| Family | Decision class | Output | Distinguishing derived fact |
|---|---|---|---|
| `module-no-decision` | `NoProverDecision` | deterministic public | Exact reconstruction algorithm/contract and no Strategy decision |
| `module-prover-decision` | `ProverDecision` | prover-only internal | Two decisions expose one `ObservedModuleValue` and one `PriorOwnMove` read |
| `module-prover-publication` | `ProverPublication` | public publication | One unique public observation and influence-output coordinate |

The typed and cold paths form all six views for every carrier and agree on 18
distinct exact bodies. Every body round-trips, sorted-unique collections use
exact target-child-byte order, and repeated projection from immutable owner
bearers is byte-identical.

The frozen gate has 69 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 18 |
| `Refused` | 33 |
| `MissingDependency` | 4 |
| `KindMismatch` | 2 |
| `Malformed` | 1 |
| `Unsupported` | 1 |
| `CannotAnswer` | 10 |

## 3. Design consequences

### 3.1 Core identity binds module references but does not supply preimages

`ModuleEffectRef` carries an exact semantic-module reference, declaration
kind and local ordinal, and payload. The Core's identity therefore commits to
that reference. The Core body does not contain the referenced declaration
body, however. A clean-room evaluator cannot derive the decision class,
payload ABI, output visibility, reconstruction law, control dependencies, or
transfer from Core bytes alone.

The executable consequence is an exact source closure:

```text
ModuleProjectionSource(core) =
  canonical Core body
  + {(module_ref, module_body) | module_ref in core.used_modules}
```

The source keys must equal the exact directly used module owners, and each
body must authenticate its key under the selected semantic regime. Missing
availability is `MissingDependency`; an extra ambient module is refused.

This should become an explicit requirement of the eventual neutral
source/read package and Q1 checker. It does not justify embedding module
bodies into every normalized view. The views may retain exact references once
the package/checker has authenticated the dependency closure.

### 3.2 Exact evaluator support is a capability, not new semantic authority

A well-formed semantic-module declaration is not automatically executable by
every zkc evaluator. The module preimage first determines semantics; the
evaluator must then advertise support for the exact module/declaration body.
An unknown same-kind body returns `Unsupported`, while wrong kinds,
coordinates, malformed payloads, and violated owner laws keep their distinct
fail-closed outcomes.

This boundary belongs with existing admission capability and evaluator
fingerprinting. A `ModuleKernel` would duplicate the module's own declaration
identity and obscure who owns support.

### 3.3 Module output coordinates are SSA-like without becoming tokens

Every module output has one stable definition coordinate
`OccurrenceOutput(occurrence, output_ordinal)`. A later module payload may name
that value, and a later Strategy decision may derive an
`ObservedModuleValue` read. A prior prover decision independently yields a
`PriorOwnMove` read. These are typed, coordinate-preserving owner projections.

That is the useful SSA property: unique definitions and explicit uses. It
does not require an authored transcript variable or a token threaded through
PIR. An MLIR token may later enforce lowering order, but it cannot replace the
Core schedule, semantic-module declaration, or owner-derived read set.

### 3.4 Causal edges and semantic transfer are separate

The module declaration provides ordered dependencies for each
`ModuleControl` and `ModuleOutput`. The Core occurrence supplies the activity,
effect, payload producers, and ordinary occurrence-output coordinates. The
resulting PCGraph contains explicit edges among those nodes.

Classification is not a blind join over graph adjacency. The declaration
also selects one local output transfer:

```text
Deterministic(inputs) -> inherited class
Publish(inputs)       -> public observation when inputs are public
PrivateMove(inputs)   -> prover-private class
```

This separation lets the graph preserve all causal dependencies while the
transfer carries the semantic effect of deterministic reconstruction,
publication, or a private prover choice.

### 3.5 Admission is not FS admission

All three positive carriers pass Core admission and same-evaluator Fresh
pairing. Their same-Core structural FS eligibility differs:

| Family | PCGraph | Eligibility |
|---|---:|---:|
| deterministic no-decision | 11 nodes / 15 edges | true |
| private prover decision | 16 nodes / 25 edges | false |
| prover publication | 11 nodes / 15 edges | true |

The private module's prover-only output reaches acceptance-relevant module
sinks and therefore fails structural public-coin eligibility. The publication
module applies the explicit publication transfer and exposes the required
public observation. Neither Core admission nor a `ProverDecision` label alone
answers the FS question.

This is the structural seam needed by later checked Fresh-to-FS construction,
but it is not a BCS, RBR, duplex-sponge, concrete-instantiation, or QROM
theorem. Those regimes remain Analysis-owned questions over an exact admitted
subject and exact construction evidence.

### 3.6 Deterministic outputs require executable reconstruction authority

An output classified as deterministic and public must name an exact
reconstruction algorithm and contract. The typed path authenticates their
preimages, exact module closure, total ABI, and identities. The cold path
independently reconstructs the fixture's expected references and verifies
that the authenticated module declaration names them.

This prevents an output from being called deterministic because a producer
asserted that the verifier could recompute it. General reconstruction
semantics, execution, and receipt validation remain later work.

## 4. Mutation closure

Twenty-eight freshly authenticated semantic mutations cover:

- payload arity, temporal availability, and ABI;
- module/declaration owner equality, kind, and local coordinate;
- exact `used_modules` and module-preimage closure;
- reconstruction algorithm, contract, module closure, and identity;
- terminal fallback and backlink shape;
- evaluator support for the exact declaration body;
- duplicate, missing, or absent declaration dependency coordinates;
- lifecycle work bounds;
- deterministic, private, and publication output visibility; and
- publication influence ownership.

Six additional values are schema-valid but owner-wrong: they omit or replace
the supported-extension atom, module move ABI, graph edge, graph class,
observed-module read, or prior-own-move read. Cold controls reject absent,
altered, and truncated module bodies, truncated Core bytes, Core body/reference
substitution, and cross-Core Protocol substitution. A genuine B2C1B3 bearer
cannot authorize the B2C1B4 projection law.

The result continues to separate:

```text
schema validity   -> can the bytes inhabit the candidate grammar?
owner equality    -> are they uniquely derived from authenticated owners?
runtime validity  -> did one execution produce a matching event history?
```

B2C1B4 supplies bounded evidence for the first two only.

## 5. Program accounting and next gates

B2C1B1 through this slice now cover 20 of the 21 B2C pressure families at
bounded research resolution:

| B2C slice | Families | State |
|---|---:|---|
| Foundation | 4 | Complete, bounded |
| Oracle | 8 | Complete, bounded |
| Claim/Reduction/Challenge | 5 | Complete, bounded |
| Module decision/publication | 3 | Complete, bounded |
| Expanded Terminal behavior | 1 | Open as B2C1B5 |
| **Total** | **21** | **20 covered, 1 open** |

B2C1B5 should now isolate Reject/Abort, Consume/Discharge, first-active
terminal preemption, and path-sensitive Claim/Reduction closure. B2D then
combines all PCGraph classes and validates completed Fresh run/receipt
descriptions. F0-V2C may decide publication and profile rotation only after
those gates expose no unresolved owner-body contradiction.

The main-design requirements to carry forward are:

1. make the exact used-module preimage closure part of the source-package
   contract;
2. retain exact evaluator support fingerprinting for module declarations;
3. derive module decisions, reads, outputs, controls, graph edges, and
   eligibility from existing module/Core owners;
4. keep admission, Fresh pairing, FS structural eligibility, and security
   theorem judgments distinct; and
5. keep missing source or support fail closed rather than synthesizing a
   negative or affirmative property result.

## 6. Non-claims

This checkpoint does not:

- execute a module, reconstruct an output, or validate a completed module
  event history;
- define or support a general extension-module language;
- close expanded Terminal semantics or either B2D integration family;
- publish or migrate a target profile;
- establish correspondence with the current zkc compiler or runtime;
- prove the candidate projection, a compiler refinement, or target semantics;
- establish soundness, a random-oracle theorem, Fiat--Shamir security, or a
  concrete hash/sponge claim; or
- close F1 Q1 correspondence.
