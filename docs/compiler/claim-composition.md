# Execution-bound conditional claims

The compiler has an optional production claim checker and registered `claim`
dialect alongside PIR. The source, the caller's authoritative contract and the
candidate derivation are three separate inputs. Deleting a candidate graph cannot
delete the caller's requirement. The checker uses the maintained
[`Analysis/Obligations`](../../compiler/include/zkc/Analysis/Obligations.h) kernel
for ordered logical closure; it does not implement a second closure algorithm.

This is a bounded implementation contribution to the application composition,
not a cryptographic security theorem. The source-binding implementation
described here has no new Lean correspondence theorem. The existing differential
evidence for the generic closure kernel establishes only its structural closure
behavior.

## Design and authority

Three alternatives were considered against the actual source and construction
interfaces:

| Alternative | Consequence | Decision |
|---|---|---|
| Inline source AST requirements/reductions/regions | Changes authoring, owned nodes, every interchange reader and round trip, identity and runtime consumers together | Deferred until a general authoring language is designed |
| Separate compiler-owned typed contract plus original source | Preserves the runtime ABI; allows independent requirements and exact source correspondence; needs an explicit caller authority boundary | Implemented |
| Protocol summaries alone | Useful for scale, but a function symbol or signature cannot establish execution binding or a law | No opaque/blanket summaries in this implementation |

The public owned API is
[`zkc/Claims/Claims.h`](../../compiler/include/zkc/Claims/Claims.h).
`Contract` contains extensible predicate signatures, exact predicate instances,
requirements, operational terminals, trust laws and bound rules. `Certificate`
contains only two fingerprints and an ordered list of already admitted rule
names. Every call checks the current typed input; no mutable record receives a
cached admission status.

The caller supplies the contract independently of the candidate. The compiler
cannot decide whether a caller chose the intended application predicate or
whether a proposed body law is true. The only supported law-authority form is
an explicit recorded `trust` premise with nonempty explanatory text. A candidate
cannot introduce a law, kind, requirement or source binding. Running a caller
contract builder again on changed source is a new caller assertion of the body
laws, not mechanical revalidation of their mathematical or security meaning.
The caller must own or authenticate source, contract and construction policy.
Neither their file location nor their mutual hashes authenticate them. Replacing
that entire trusted configuration is a change of authority, not a candidate
transformation this checker can reject on its own.

A successful check means: **conditional on the supplied body laws, installed
primitive and execution semantics, and the checked source/artifact
correspondence, successful completion of the selected validator's execution
supports every independently retained requirement.** It does not establish
standalone predicate truth, knowledge extraction, soundness error, probability
bounds, Fiat–Shamir security, zero knowledge or relation adequacy. A PCS verifier
success becomes an operational guarded fact; its relationship to a mathematical
opening remains an explicit law premise.

## Actual execution binding

The checker performs the existing structural/source admission and generic
preparation before analyzing a selected entry. It expands the admitted common
source's actual selected instances, local calls and bounded loop iterations.
The resulting catalog is a symbolic control/binding expansion, not a concrete
runtime execution trace and not a second execution engine.

* Root arguments receive distinct value identities and retain ordinary logical
  types. Operations produce new identities. Local/protocol returns substitute
  their actual returned identities into the caller. Loop-carried inputs use the
  preceding iteration's actual yielded identities; zero iterations return the
  initial identities.
* A received message gets a separate identity. The checker never assumes that
  an adversarial participant sent the value computed by an honest producer.
* Invocation paths use numeric source positions, recursively including concrete
  loop iteration positions. Site labels are not invocation authority. Each rule
  must match the resolved callee and the complete ordered input/result vectors
  of that specific invocation. Function-name agreement is insufficient.
* An operational terminal binds the **exact Boolean consumed by an actual
  installed `control.require`**, owned by the contract's validator role. A
  comparison, unused Boolean, prover-only guard, declaration or zero-trip loop
  supplies no such fact. Required guard anchors on rules must belong to the
  selected invocation. A rule may not manufacture a built-in `guard` claim.
* The source's installed affine-resource admission remains mandatory. RNG,
  transcript, nonce, capability and opening-state objects cannot be logical
  predicate operands. Repeated logical evidence does not execute a call again
  or mint a resource. Mathematical/key/commitment values retain ordinary types.
  This adds no new entropy, independence or resource-distribution theorem.

Rule subjects and residuals are the exact value-ID tuples in the authoritative
claim table. The caller's law determines what those tuples mean. The checker
checks their exact types, identities, invocation and source body. It does not
infer a missing relationship between distinct same-typed values. Equal predicate
kind/value tuples are interned for logical reuse; distinct tuples remain distinct
requirements. Repeating one derivation cannot cover another requirement.

The source fingerprint is lowercase SHA-256 over
`"zkc.execution-claims.source/1\n"` followed by compact `printJson(encode(original))`.
It includes the entire original source, generic definitions, selected bindings,
dependencies, static parameters, bodies and unused declarations. The contract
fingerprint similarly uses `"zkc.execution-claims.contract/1\n"` and its complete
encoded contract. Text comments/formatting and diagnostic locations are not
serialized. Source names and site spellings are serialized. An unrelated source
change can conservatively invalidate every law. Fingerprints establish
correspondence, never the law itself.

## Interchange and commands

Source and construction descriptors use the existing `.pir` or array JSON.
Contract and certificate input use the existing strict portable array parser;
ordinary JSON objects, extra fields, malformed strings and incorrect shapes
are rejected. All identifiers below are strings, including value and path IDs.
The inspection report uses ordinary object JSON for authoring tools.

```text
["zkc.claim-contract/1", SOURCE_DIGEST, ENTRY, VALIDATOR_ROLE,
  [[KIND, [TYPE, ...], MEANING], ...],
  [[CLAIM, KIND, [VALUE_ID, ...]], ...],
  [REQUIRED_CLAIM, ...],
  [[TERMINAL_CLAIM, GUARD_PATH], ...],
  [[LAW, "trust", PREMISE_TEXT], ...],
  [[RULE, LAW, INVOCATION_PATH, CALLEE,
    [INPUT_VALUE_ID, ...], [OUTPUT_VALUE_ID, ...],
    [GUARD_PATH, ...], [PREMISE_CLAIM, ...], CONCLUSION_CLAIM], ...]]

["zkc.claim-certificate/1", SOURCE_DIGEST, CONTRACT_DIGEST, [RULE, ...]]
```

The built-in predicate `guard` takes one `bool` operand and cannot be redeclared.
User kind signatures use exact source logical type spellings. Terminal records
only produce `guard` facts. Rules may be premise-free for caller-admitted pure
connection laws; this is explicitly a trust premise, not an inferred axiom.
Requirements are independent of certificate steps. An explicitly empty caller
specification is legal.

```sh
zkc-compile claim-inspect source.pir main > catalog.json
zkc-compile claim-derive source.pir contract.json > candidate.json
zkc-compile claim-check source.pir contract.json candidate.json
zkc-compile claim-import source.pir contract.json candidate.json > claims.mlir
zkc-opt claims.mlir --pass-pipeline='builtin.module(canonicalize,cse,symbol-dce)' > selected.mlir
zkc-compile claim-check-ir source.pir contract.json selected.mlir
zkc-compile claim-check-construction source.pir contract.json candidate.json descriptor.pir construction.json
zkc-compile claim-check-lowering source.pir contract.json candidate.json descriptor.pir construction.json physical.json
# The last command also accepts --linear-contractions for that selected lowering.
```

`claim-inspect` reports source fingerprint, selected entry/roles, values
`{id,type,origin,name}`, invocations `{path,callee,instance,inputs,outputs}`, guards
`{path,value,role}`, loops `{path,count}` and operations
`{path,callee,inputs,outputs}`. Operation callees are installed logical contract
names. Invocations preserve actual specialized source callable names. Names in
value records are diagnostic authoring help; IDs refer to this exact admitted
source snapshot.

## Registered representation and artifact custody

`claim.kind` and `claim.law` are symbol declarations. `claim.binding` exposes a
derived source-value binding with its ordinary logical MLIR type;
`claim.invocation` uses those SSA operands for the actual inputs and outputs.
`claim.loop` records a concrete count, while the catalog and binding operations
contain the actual expanded iterations. One loop marker never supplies evidence
for all iterations.

`claim.pending` constructs a pending proposition using typed SSA subjects and a
kind symbol. It produces `!claim.pending`, not evidence. `claim.require` records
independently retained requirements. `claim.terminal` binds a pending guard claim
and its exact source Boolean. `claim.rule` records a trust-law symbol and actual
invocation/guard bindings. `claim.apply` consumes previously available
`!claim.evidence` and references a rule symbol. `claim.finish` consumes evidence
for every original requirement. Evidence is reusable logical data.

The ordinary MLIR verifier establishes representation structure only.
`claims::checkIR` extracts candidate rule applications, rechecks closure against
the caller authority, reconstructs the source-derived representation and compares
operations, attributes, symbols, types and SSA correspondence. Source locations
and printed SSA names may differ. Deletion, subject substitution, added regions,
changed law metadata and arbitrary scheduling are not accepted as equivalent.
Canonicalization/CSE/symbol DCE are tested on the conservative operations; there
is no advertised general claim optimizer or automatic check-elimination pass.

The graph is never accepted as executable PIR. None of these APIs erases runtime
checks. `checkConstruction` reconstructs the expected certificate with the
**same original source**, descriptor, entry and validator role, then compares
the candidate. The descriptor remains an independently supplied caller policy:
claim admission does not prove that its public-binding map or challenge profile
satisfies a particular cryptographic law. The application validators separately
check their required public-binding maps. The same interactive contract may be
used with multiple constructions under separately admitted construction laws.
`checkLowering` additionally reruns the existing projection, physical lowering
and export from that checked construction and compares the actual physical JSON.
The shared `PhysicalOptions` selects installed implementation choices, optional
linear contractions and optional ordinary storage release (`releaseStorage`).
The physical compile and claim-check CLI accept the same `--implementations`,
`--linear-contractions` and `--release-storage` selections. Source-bound choices
are checked against the recomputed construction's common source. The checker
compares the complete candidate including ordered releases; it does not erase
unvalidated operations or regenerate caller authority from the candidate.
Other transformed artifacts need their own supported correspondence procedure;
a valid claim graph cannot authorize them. Recomputing this named pipeline is
custody checking, not an independent proof of its refinement laws.

## Bounds and refusals

The selected scope is closed, admitted common source with known operations,
nonrecursive instances, straight-line local bodies and fixed bounded protocol
loops. External bodies, explicit stop/incomplete nodes on expanded paths,
participants as original source, unsupported branches/regions and unknown
operations are rejected. Supported primitives may fail according to their
existing semantics; claims are conditional on a successful validator run.
Unreachable zero-loop bodies provide no facts. No induction, dynamic scope,
recursive proof, blanket loop summary or future region-authoring DSL is claimed.

Files use the existing 1 MiB source/contract/certificate limit and 64 MiB MLIR
limit. Direct typed contracts also have 32,768-element per-list limits,
200,000 aggregate entries, 4,096-byte strings and a 1 MiB total string budget.
Expansion has depth 64 and a 200,000 work budget charging instructions, created
values, actual operand lists, trip counts and per-iteration carried/captured
bindings. The physical/construction path retains its own existing limits.
Certificates may repeat rules, but their expanded premise occurrences are
limited to 200,000 before checking or constructing SSA operands. The underlying
obligation API separately caps expanded checking work at 4,194,304 premises.
Oversized supported-looking instances fail instead of acquiring an opaque
summary. MLIR candidate checking requires a flat block with no nested regions
and bounds operation count before verification. Textual nesting is limited to
64 before entering the recursive MLIR parser; quoted text and comments do not
contribute to that limit.

The compiler reports stable diagnostic identifiers:

| Diagnostic | Refusal |
|---|---|
| `claim-source`, `execution-entry`, `claim-validator` | Wrong original input kind, missing entry or validator role |
| `claim-contract-format`, `claim-certificate-format` | Invalid schema or bounded typed input |
| `claim-source-mismatch`, `claim-certificate-mismatch` | Stale source/authority |
| `claim-kind`, `claim-subject`, `claim-resource-subject` | Unknown/bad predicate signature, wrong value/type or resource subject |
| `claim-duplicate`, `claim-reference`, `claim-authority` | Duplicate declaration, absent claim or absent caller law |
| `claim-invocation`, `claim-guard` | Wrong actual call binding or unenforced/wrong-scope/role Boolean |
| `claim-rule` | Candidate selects a rule absent from caller authority |
| `execution-expansion-limit`, `execution-unsupported-scope` | Expansion budget or unsupported execution structure |
| `execution-local-control-static-trace` | Local conditional, for-loop, match or variant construction cannot be expanded by the static claim trace |
| `source-execution-family-input-required` | An invocation-selected loop count requires actual family inputs |
| `claim-analysis-limit` | Excessive closure data or expanded certificate work |
| `claim-ir-depth-limit` | MLIR nesting exceeds the pre-parser bound |
| `claim-ir`, `claim-ir-mismatch` | Invalid or source-inconsistent MLIR |
| `claim-construction-binding` | Descriptor entry/validator differs from contract |
| `claim-lowering-mismatch` | Actual physical output differs from prescribed lowering |
| `claim-lowering` | Existing lowering itself refuses; its detailed diagnostic precedes this wrapper |

The existing closure kernel supplies `claim-unresolved`,
`claim-premise-unavailable` and its own index/analysis bounds. Existing source,
parser and construction refusals propagate without being disguised as claims.
The tests assert the documented externally reachable refusals. `claim-lowering` is a
wrapper for existing lowering diagnostics rather than a distinct semantic rule.
