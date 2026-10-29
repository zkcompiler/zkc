# Source obligations and Lean companions

A companion is an ordinary Lean theorem or definition selected for an already
fixed obligation. Source identity supports discovery; only checking the exact
expected Lean type, premises, axioms and subject can discharge the obligation.
This contract is frontend-owned. Lean's resolver and existing declaration,
bound-request and receipt pipeline own elaboration and proof admission.

## Lookup identity

A lookup key is the compact JSON serialization of this ordered array:

```
["zkc.companion/0", owner, selection, role, local_key]
selection = ["template"] | ["instance", symbol]
local_key = ["label", text] | ["ordinal", decimal_string]
```

Strings use JSON escaping and UTF-8; there is no whitespace outside strings.
The ordinal is a canonical nonnegative decimal string. `owner` is the canonical
qualified source declaration that owns the obligation. For a named audit it is
that audit's qualified name; an anonymous owner spec uses its protocol owner.
Anonymous consumer audits use their written `{owner,path}` source identity in
the enclosing inventory, and require an explicit audit name before reusable
companion registration. This prevents two anonymous audits from sharing a key.

`symbol` selects an actual closed instance in the checked instance inventory.
Its template/substitution must be checked against that inventory; decoding a
printed symbol is not a proof of origin. Instance lookup is scoped to the fixed
capture, installation and Lean dependency environment. These artifact digests
are mandatory context, but are excluded from the reusable lookup string so that
editing a body does not require renaming an authored theorem.

Roles are `postcondition`, `request`, `source-correspondence`,
`implementation-law`, `realization-correspondence` or `stage-link`. These labels
classify obligations; they do not register new semantic links. A stage link's
actual identifier must be admitted by Lean's registry. Additional roles require
a contract and producer/consumer change.

Explicit source labels supply `local_key`. Otherwise, clauses are numbered in
source order within their semantic role and owning spec, including labeled
clauses. Inserting or reordering an unlabeled clause can change its key. The
fixed expected type is rechecked even when a key survives an edit. A changed
postcondition cannot inherit a proof merely because its ordinal is unchanged.

## Obligation inventory

Every declared `ensures` contributes a mandatory postcondition obligation.
Every requested property contributes a request obligation. Neither requires an
explicit clause label or membership in another security bundle. `requires`
contributes a premise of its owner's obligations; `target` and `reduces` supply
relation data interpreted by their registered request families. They do not
silently become a claim of security on their own.

The frontend's pending inventory is an authored obligation inventory, not a set
of elaborated propositions. Each item retains its role, optional label, ordinal,
source span and unresolved state. Lean elaboration replaces a pending item with
its fixed proposition and exact subject; it must preserve complete required
coverage. A missing postcondition proof remains open even if another requested
property is certified.

An omitted postcondition cannot be inferred from author intent. A separately
consumer-owned expected request set prevents an omitted or weakened requested
property from satisfying that consumer. The set is fixed before examining
receipts and bound to the exact selected subject/environment. A missing spec
still permits ordinary native execution and reports `no-claim`, never security.

## Resolution

The assembler supplies instance-specific selection first, then template selection
with independently fixed argument substitutions. Missing instance registrations
permit template lookup. A present duplicate, ill-typed or incomplete instance
must not fall back to a template. Registrations from imported modules count only
when their declarations are visible. Repeated registration of the same theorem
is harmless; competing theorem declarations are ambiguous.

The expected type contains no unresolved metavariables before lookup. Instantiate
the selected declaration, elaborate its supplied arguments, synthesize obligations
and kernel-check the resulting term against that type. Roll back failed
elaboration. `sorryAx`, unsolved metavariables and proof/definition-wanted stubs
are incomplete, never proof evidence. A matched theorem still passes the owning
receipt's assumption and stage-link policy; lookup does not bypass that audit.

Resolver results are `matched`, `missing`, `incomplete` or `refused`. These describe
lookup, not assurance. Missing/incomplete obligations remain open in the inventory;
refusal reports its cause. The receipt pipeline alone emits assurance states
such as `certified`, `open`, `incomplete` and `no-claim`, with outcomes
`established` or `unresolved` for its exact audited scope.

## Generated modules and author files

The import order is reusable library → generated definitions/obligations →
authored companion → generated assembler. The assembler imports the generated
obligations and companion and resolves the fixed expected types. Generated
source/obligation modules must not import their own companions. Reject import
cycles before building.

A scaffold writes only a missing author file; regeneration never overwrites an
existing companion. Removed keys are reported as orphaned registrations. Source
paths and editor navigation are metadata, not semantic identities. Generated
files live in a replaceable build directory. Ordinary Lean tooling handles proof
editing in the captured Lean project.

No parallel `zkc.lean-interface/0` pipeline is introduced. Exported declaration
metadata extends `zkc.declarations/0`; requests use `zkc.bound-source-claims/0`;
subjects and receipts use their existing independent readers and
`lean/checks/check_records.py`. Metadata and companion registration never
manufacture proof authority.

## Consumer requirements transport

`lean/checks/check_records.py --subject NAME --requirements PATH` passes an
independently supplied JSON object into the existing fresh Lean receipt audit.
The file is not read from a provider's subject manifest and is never synthesized
from the receipts under inspection. It uses this exact outer shape:

```json
{
  "format": "zkc.consumer-requirements/0",
  "context": {
    "subject": "consumer-selected subject name",
    "manifest_sha256": "exact selected manifest SHA-256",
    "checker": {"...": "complete independently selected checker environment"}
  },
  "claims": [
    {"node": {"kind": "source-claim", "owner": "qualified owner", "block": 0, "claim": 0},
     "request": {"...": "complete admitted request, including exact subject and stage"}}
  ]
}
```

The ellipses illustrate complete existing records, not literal wildcard fields.
The checker object uses the existing assurance-report environment schema. The
request is the full `zkc.bound-source-claims/0` request object, not a property name
or digest alone. Its attachment node identifies the required occurrence under
that context. A consumer copies or authors this policy independently before
inspecting a candidate's receipts and refreshes it deliberately when changing
accepted artifacts. Pinning a manifest does not prove its source correspondence.

Lean compares exact JSON values and requires a nonempty, unique expected
occurrence set. Every expected occurrence must appear exactly once with exactly
that request and obtain a certified receipt from the existing audit. Missing,
changed, ambiguous or unproved requirements leave the result open. Extra claims
are still audited under the existing selected-scope rules. An all-empty provider
inventory cannot downgrade requested work to `no-claim`. A matching requirement
set alone proves nothing; ordinary registry, subject, dependency, kernel and
stage checks remain mandatory. Trials are separate scopes and do not discharge
requirements of the selected subject.

The final audit echoes the requirement object, bound to the fresh invocation's
nonce and input digest. The report retains it. Transport failure remains a
transport failure. The CLI returns failure when explicit consumer requirements
are unresolved. Without this option, an established outcome describes only the
provider's declared scope; it makes no assertion about unlisted consumer needs.
Duplicate JSON members and non-finite JSON numbers are refused at file ingress.
The Lean audit rejects unknown or missing fields in the requirements object,
its context and each expected-occurrence item. Extending these records requires
an owning contract and consumer change rather than ignored policy metadata.
