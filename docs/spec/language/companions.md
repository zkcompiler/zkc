# Source obligations and Lean companions

A companion is an ordinary Lean theorem or definition selected for an already
fixed obligation. Source identity supports discovery; only checking the exact
expected Lean type, premises, axioms and subject can discharge the obligation.
This contract is frontend-owned. Lean owns elaboration and proof admission.
The source inventory and lookup addresses remain supported; the former native
subject/receipt connection pipeline is retired. The current common framework
checks typed companions, but installation against actual exported source is
still open. See [formal support](../../../lean/docs/support.md).

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

Roles are `postcondition`, `request`, `oracle-admissibility`, `source-correspondence`,
`implementation-law`, `realization-correspondence` or `stage-link`. These labels
classify obligations; they do not register new semantic links. A stage link's
actual identifier must be admitted by Lean's registry. Additional roles require
a contract and producer/consumer change.

Explicit source labels supply `local_key`. Otherwise, clauses are numbered in
source order within their semantic role and owning spec, including labeled
clauses. Inserting or reordering an unlabeled clause can change its key. The
fixed expected type is rechecked even when a key survives an edit. A changed
postcondition cannot inherit a proof merely because its ordinal is unchanged.

### Virtual-oracle admissibility

An oracle definition has one `oracle-admissibility` address for its complete
generated Formula predicate, with `local_key = ["ordinal", "0"]` and no label.
The owner is the authored oracle's canonical qualified name. Closed selection
uses the oracle constructor's actual instance symbol, rather than the generated
Formula's symbol. The checked instance inventory binds this selection to its
template and exact static arguments, including nominal source types.

The whole predicate includes every ordered authored `requires` clause and
every generated source row-bound conjunct. This also covers definitions with
only generated bounds or an empty conjunction. Authored labels and ordinals
remain inspection metadata. Clause-level keys would require a separate coverage
and conjunction-assembly contract for generated bounds and empty predicates;
using the existing Formula avoids a second semantic authority.

The definition address alone is not a construction obligation. Each retained
construction contributes an unresolved occurrence with the actual source
anchors and ordinary captures. The [source-instance export](source-ast.md#closed-source-instances)
retains these occurrences independently of optional security selection. A loop
body occurrence represents each reached construction under that loop's context;
its row is not a theorem about every iteration. Consumers fix the full Formula
application and its context before lookup and check its exact expected type,
nominal specialization and actual input substitution. Reusing an address after
editing a predicate never reuses proof evidence without that check.

## Obligation inventory

Every declared `ensures` contributes a mandatory postcondition obligation.
Every requested property contributes a request obligation. Neither requires an
explicit clause label or membership in another security bundle. `requires`
contributes a premise of its owner's obligations; `target` and `reduces` supply
relation data interpreted by their registered request families. They do not
silently become a claim of security on their own. A target's explicit `accept`
expression is authored relation-to-decision data, awaiting typed interpretation.
The native pending inventory does not certify that association.

`security:` is a grouping production, not a label. Each contained request has
its own explicit label or its position in the spec's request sequence. Group
boundaries do not restart that sequence, introduce an obligation, or introduce
a label namespace. Inline `security: expression` contributes one anonymous
request. Duplicate explicit request labels refuse across the whole spec.

Within an oracle definition, `requires` instead contributes to the generated
admissibility predicate whose construction occurrences are mandatory, as above.

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
are incomplete, never proof evidence. A matched theorem must still satisfy the owning claim's assumption and
stage-link policy; lookup does not bypass that audit.

Resolver results are `matched`, `missing`, `incomplete` or `refused`. These describe
lookup, not assurance. Missing/incomplete obligations remain open in the inventory;
refusal reports its cause. A claim's checked proof and complete required coverage must be established
separately. The retained declaration-record audit reports neither native
certification nor a source/security connection.

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

The maintained `zkc.declarations/0` records audit stored Lean declarations,
axioms and locked theorem statements. They are not a bound source-request or
receipt format, and `lean/checks/check_records.py` does not take native subject
or consumer-requirement inputs. Metadata and companion registration never
manufacture proof authority.

## Independent required coverage

A consumer fixes its expected obligations independently of the proofs supplied
by a provider. That set must retain the exact selected subject, source
occurrences, interpreted propositions and dependency context. Names and digests
alone cannot replace these records or prove source correspondence.

A valid theorem and complete declaration coverage are distinct judgments.
Missing or unproved requirements keep coverage open without invalidating an
otherwise valid theorem. A direct kernel-checked proof of a fixed claim does
not need a registered-law route, and cannot silently discharge unrelated
public promises. Author-only coverage does not establish security.

Actual-source installation and coverage reporting are future consumers of this
contract. The retired receipt transport and command-line interface are not
retained as compatibility routes. Frontend tools must not present pending
inventory, successful lookup or declaration metadata as native certification.
