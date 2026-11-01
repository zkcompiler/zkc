# Structured verifier observations and public-coin requirements

The native public-coin checker reads an explicitly selected **authored** or
**realized** Protocol IR subject. It produces a bounded, conservative verifier
observation DAG. This is an actual-source structural judgment, not transcript
binding, Fiat–Shamir security, provider conformance, or a semantic simulation.
Dependency is not binding: an expression such as `x - x` can depend syntactically
on `x` without encoding it injectively.

The analysis owners are [protocol observations](protocol-observations.md) and
[execution observations](execution-observations.md). Shared protocol and
numerical definitions remain shared. Repeat bodies have finite transfer
summaries including zero iterations; the report never unrolls them into an
alleged execution trace. Logical stops remain distinct from host budgets and
allocation failures.

## Independent selection and ownership

`zkc.public-coin-requirement/0` is an exact JSON object:

```json
{
  "format": "zkc.public-coin-requirement/0",
  "subject": "authored",
  "entry": "main",
  "deployment_entries": ["main"],
  "prover": "P",
  "verifier": "V",
  "service": 0,
  "decision": 0,
  "bound_inputs": [],
  "draws": [{"query_site": "draw", "delivery_site": "coin"}]
}
```

The two subject choices are different judgments. There is no fallback between
those choices. The entry has exactly the named two roles. `service`, `decision`
and `bound_inputs` address the selected subject's **actual** common signature.
The decision is a verifier-available Boolean result; the selected random service
is owned exclusively by the verifier. Every verifier data input must be listed
in `bound_inputs`, even if unused. Bound inputs must have a wire data policy;
service references are separate authority, never bound data. A realized
signature can contain generated shape inputs. Those are explicit obligations,
not implicitly covered by an original logical oracle handle.

`deployment_entries` is a nonempty, duplicate-free inventory containing `entry`.
It identifies the complete retained preparation/realization context, including
companion entries required by other checks in a compiled invocation. This is
independent input, not inferred from a supplied report. The inventory must match
the checked owner's actual retained programs exactly. Report order is canonical;
requirement byte identity still distinguishes differently written requests.

Mathematical selection and oracle realization policies are independent API/CLI
inputs. Standalone analysis prepares once, selects this inventory, and realizes
once through the existing actual-body checker. Checked compilation uses its
already constructed owner. The owner retains authored source, prepared source,
realized candidate, requested policy, normalized root selection, and checked
realization record. The checker never constructs a second preparation inside a
compiled invocation or accepts a report's policy as authority.

Authored analysis uses the retained source with shared applications intact. It
refuses logical oracle effects rather than treating a handle as received data.
Realized analysis uses the checked candidate. Exact generated opening-request
exchanges are selected by the checked realization owner as deterministic
transport. A label, source attribute, or untrusted report cannot authorize this
classification. These sends require empty pending-challenge state and do not
consume a challenge. Other verifier sends must forward the exact pending draw.

## Observation and challenge families

The selected verifier's service queries must all use the selected entry service,
including through actual call substitutions. A field draw, scalar index draw,
and product index-sequence draw retain different request laws. The admitted
positive static request operands, their actual SSA associations, and their
dependencies remain explicit.
No request law proves provider sampling conformance or provider-specific domain
admission by itself.
Prover-private queries do not become verifier challenge families.

The independent `draws` list selects query/delivery pairs in structural traversal
order. A shared helper invoked twice denotes two contexts. Selector spelling is
the same left-fold application-site spelling used by preparation; the report
also retains the structured path and actual operation/context references. A
repeat contributes one family with an iteration-coordinate template, not one
freshness assertion for all iterations. Repeats do not add a spelling segment.
Labels grant neither entropy nor cryptographic domain separation.

The observation transfer checks exact forwarding separately from dependence:

- a new query requires empty pending state;
- a verifier receive requires empty pending state and creates an independent
  observed atom, even if the sender used an expression also known to V;
- a challenge delivery consumes the exact pending query through admitted aliases
  and call forwarding; reconstruction from arithmetic dependencies does not pass;
- helpers can query and return a challenge for another helper to deliver;
- repeated bodies must preserve incoming pending state or form a closed round
  for every count, including zero;
- a root cannot require an incoming pending formal or leave a pending query.

Verifier guards and eager numerical calls contribute logical-stop dependencies,
including zero-result or ignored-result calls. Unknown verifier effects refuse.
The result is conservative may-dependence, not a path-feasibility proof. The
interface separately records statement inputs, bound nonstatement inputs, and
bound inputs unavailable to the prover. Verifier-only data is not thereby made
available for a prover-computed transcript.

## Report

`zkc.public-coin-view/0` records the subject, entry/deployment inventory, roles,
service/decision indices, actual interface, and a `graph` containing:

- `root`: the selected definition ID;
- `definitions`: first-use IDs for actual protocol definitions and retained
  repeat bodies, qualified by the observing role;
- `numerical`: shared actual numerical definitions and reachable interpretation
  premises;
- `draws`: selected query families and exact delivery occurrences, with actual
  call contexts and symbolic iteration coordinates.

Each protocol definition includes its declaration, block owner, formal types,
atom basis, ordered actions, result/stop/service dependencies, exact result
origins and pending transfer. Nonformal call/repeat atoms refer to actual child
result or stop transfers; they are not arbitrary messages. Actions retain actual
operation kinds, sites, attributes, typed SSA operands, observation categories,
dependencies, exact input
origins, child IDs and selected deterministic-transport status. Repeat actions
retain count/carry/capture association, maximum and the finite fixed-point
transfer rule. A null dependency vector means unavailable; an empty array means
an observed value with no dependence. Internal padding is never an atom.

Numerical rows retain actual declarations, signatures, returning/stopping facts,
formal dependency sets, direct child IDs, and primitive occurrences with actual
binding declarations, static arguments, invocation parameters and implementation
choices. An empty implementation constraint remains unselected; analysis does
not infer a physical installation. These are interpretation premises, not claims that a provider has been
verified. In particular, relation-asset identity is not a proof of digest
injectivity or permission to omit asset bytes from a binding judgment.

Operation references are stable preorder ordinals in the analyzed module;
definition IDs use first encounter in the retained DAG. No pointer is serialized.
They are local report identities, not cross-revision identifiers or hash domains.
The report contains authored, prepared, realized and analyzed IR SHA-256
identities, exact requirement-byte identity, independent policies, normalized
oracle selection and the checked realization record. These identify the native
structural association; they do not manufacture a formal simulation.

The checker parses bounded natural JSON, recomputes the whole report from source,
independent requirement and independent policies, and requires exact equality.
Duplicate object keys, non-natural numeric tokens, changed bodies, changed
policies, missing obligations and altered graph facts refuse. A successful JSON
comparison is evidence only for this closed native checking profile.

## Limits and integration

The requirement is at most 1 MiB, with at most 1,024 input/result ports and
retained deployment entries, 64 selected challenge families, and 4,096 bytes per
name. Observation retains at most 2,048 site actions, depth 64, and one cumulative
allowance of 1,000,000 work units shared with report traversal. At most 65,536
dependency indices are serialized. The complete report, including realization
association, is at most 8 MiB. IR fingerprints stream at most 16 MiB per subject.
Exhaustion is a refusal, never a truncated successful report.

The CLI modes `protocol-public-coin` and `protocol-check-public-coin` accept the
independent mathematical-selection flags and `--oracle-realization=<JSON>`.
`protocol-checked-bundle --public-coin=<file>` associates the view with exact
source and bundle byte hashes in `zkc.compiled-public-coin/0`.
`subject_to_bundle_stages` describes the route from the selected subject to those
bytes, not a PassManager trace. For an authored subject the route includes checked
preparation and oracle realization. For a realized subject those edges precede
the analysis and are not claimed as later passes. Both routes then project and
use the actual selected lowering stages. Execution, correspondence, public-coin
observation and cryptographic binding remain distinct judgments.

## Version-0 cutover

All formats remain `/0`. Producers, readers and fixtures change together:

- `subject` and `deployment_entries` are required;
- shared definition DAGs replace flat anchors/events/prefix lengths;
- all verifier inputs are obligations, including unused inputs;
- structured calls, symbolic repeats, deterministic partial numerical helpers
  and product index queries are admitted through their analysis owners;
- authored/prepared/realized identities and independent oracle policies are
  retained, with exact checked generated-request associations;
- compilation reuses its owner and reports `subject_to_bundle_stages`.

The old flat consumer and its schema are removed. No compatibility reader remains.
