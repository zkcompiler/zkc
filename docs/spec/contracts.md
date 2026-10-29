# Cross-component contract register

This register identifies the owner, normative definition and consumers of each
cross-component contract. It is an index of authority, not an additional schema
or proof registry. The linked specifications define meanings; the typed Lean
registry determines admissible proof obligations. Private research interfaces do
not override these maintained contracts.

**Lifecycle** describes an interface: `implemented`, `partial`, `planned` or
`retired`. It is distinct from an assurance status. `implemented` does not imply
that a native implementation has been proved correct. [Status](../status.md) and
[formal support](../../lean/docs/support.md) record the actual coverage.

An owner changing a contract updates its producers, independent consumers,
fixtures and owning specification together. Native schema ownership does not
transfer ownership of its independent Lean reader: changes under `lean/` are
integrated by the formal implementation owner. Generated artifacts are regenerated
from the reconciled producers, not text-merged. Version-zero changes retain one
current schema without compatibility readers.

## Interfaces

| Contract | Owner and normative specification | Producers → consumers | Lifecycle; stages and links |
|---|---|---|---|
| Written source and elaboration evidence | Frontend; [source AST](language/source-ast.md) | Written capture and checked elaborator → independent formal source checker | Partial: capture exists; grammar-neutral elaboration checking remains open. Intended closer of `source.correspondence` |
| Original structured source | IR export; [structured source](formats/structured-source.md); formal interpretation: [Lean structured source](../../lean/docs/spec/structured-source.md) | Compiler export → Lean strict reader, admission and source connection | Implemented for the documented admitted profile; unsupported semantics refuse |
| Constructed participant | IR; [constructed participant](formats/constructed-participant.md), [construction](ir/construction.md) | Construction/export → native checking and independent Lean connection | Implemented for the documented profile; `construction.checked`, `construction.source_connection`, pair links |
| Common source | Former compiler and formal import | No retained producer or reader | Retired in favor of original structured source and the Domain interpretation |
| Language/Entry interface | Frontend, with runtime admission; [Entry format](formats/entry.md) | Compiler → Host, subject driver and request association | Implemented for admitted alternatives; structural association is not source correspondence |
| Source requests | Frontend wire; [claims](language/claims.md) | Source elaborator/binding → Lean request elaboration and canonical receipt audit | Implemented for admitted source forms; fixes subject, property, stage and parameters before evidence |
| Declaration records, subject evidence and assurance report | Formal; [assurance reports](../../lean/docs/spec/assurance-report.md) | Lean elaboration/audit and artifact capture → report and frontend display | Implemented; only the canonical audit owns assurance statuses |
| Required-request comparison | Formal semantics, frontend consumer integration; [assurance reports](../../lean/docs/spec/assurance-report.md) | Independently supplied consumer requirements + bound requests/receipts → requirement audit | Partial: independent input and canonical audit comparison implemented; frontend consumer integration remains open. Missing requirements keep the aggregate open |
| Companion selection | Frontend owns identity/export contract; formal owns typed resolution and assembly | Generated expected obligations + authored Lean declarations → assembly and existing receipt audit | Partial: typed resolver exists; cross-component identity mapping remains to be pinned. No new assurance status or security meaning |
| Logical oracle interface | IR meaning; frontend spelling; [oracles](domains/oracles.md), [protocol IR](ir/protocols.md) | Source/IR declarations → realization and independent formal interpreter | Partial: logical-operation wire and executable semantics must be admitted together before claiming a formal oracle client |
| Oracle realization evidence | IR record, formal proof; [refinement](verification/refinement.md), [formal stage calculus](../../lean/docs/spec/fiat-shamir-security.md) | Selected realization and emitted artifacts → native check and independent Lean record reader | Planned formal stage. `realization.correspondence` is not yet an admitted receipt link; registration requires a fixed meaning and proof interface |
| Canonical program bytes | IR encoding; [program bytes](formats/program-bytes.md) | Compiler → independent C++/Rust readers and planned direct Lean reader | Native readers implemented. Lean currently imports rendered data; `lowering.interpreted_bytes` does not establish correctness of the renderer or native VM |
| Operation and implementation catalog | IR contracts; [values](domains/values.md), [execution](ir/execution.md), [numerical calls](runtime/numerical.md) | Native declarations → frontend/IR signatures, execution registry and formal operation interpretation | Partial: a shared family across all four faces is a design/probe gate; a native binding is not a Lean law |
| Installed transcript/Merkle suites | Runtime installations, IR signatures, formal interpretation; [external constructions](realization/external-constructions.md), [oracles](domains/oracles.md), [Lean executable model](../../lean/docs/spec/executable.md) | Installed rows → compiler selection, runtime and formal admission | Partial, with different supported sets. A suite is admitted formally only when its exact operation/representation rows have meanings |
| Occurrence and application identity | IR occurrence encoding and formal correspondence; [construction](ir/construction.md), [structured source](formats/structured-source.md) | Source capture, applications and normalization → transcript construction, requests and connection | Partial shared map: preserve exact occurrence bytes and dynamic coordinates; relocation proposals are not proof evidence |
| Gated random requests | IR request format, runtime service, formal distribution law; [public coin](ir/public-coin.md) | Request construction → service and formal challenge interpretation | Planned joint extension; a probability bound must use the admitted actual distribution and query accounting |

## Registered vocabularies

### Assurance and stages

[Assurance reports](../../lean/docs/spec/assurance-report.md) owns these distinct
namespaces:

| Namespace | Values | Authority |
|---|---|---|
| Per-request assurance | `incomplete`, `open`, `certified`, `transport-failure` | Fresh canonical Lean audit/export and its transport validation |
| Aggregate outcome | `established`, `unresolved` | Nonempty requested set and its audited rows |
| Empty request scope | `no-claim` | Explicit empty source export; never positive evidence |
| Proof attempt result | Includes `unsupported`, `timeout`, `refused` | Diagnostic method execution, not semantic assurance |

Frontend availability, editor cancellation and companion-resolution states belong
to their own tagged results. They must not replace assurance statuses or make an
unrequested/omitted claim appear certified.

The current stage constructors are `interactive`, `compiledIdeal` and
`executableBytes` in [Wire](../../lean/Zkc/Claims/Wire.lean). Their wire spellings
are defined by the request format. A new transformation stage requires its own
objects, relation, preservation theorems and required links; adding a string to a
report does not establish it.

The installed infrastructure link families are defined in
[StageLinks](../../lean/security/ZkcSecurity/Claims/StageLinks.lean),
[DomainSubject](../../lean/security/ZkcSecurity/Claims/DomainSubject.lean) and
[CanonicalAuthorityPair](../../lean/security/ZkcSecurity/Claims/CanonicalAuthorityPair.lean):

| Family | Link identifiers | Exact obligation selected by |
|---|---|---|
| Compiled validator | `construction.checked`, `construction.source_connection` | Actual typed subject, source, role, ABI and participant |
| Interpreted executable validator | `lowering.interpreted_bytes`, in addition to the compiled links | Exact program, installed interpretation and lowering relation |
| Honest pair | `pair.checked`, `pair.source`, `construction.checked`, `pair.occurrences`, `pair.producer_connection`, `pair.validator_connection` | Actual selected producer/validator pair and source target |
| Written-source trust boundary | `source.correspondence` | Recorded trusted premise; currently not discharged by a source-elaboration theorem |

Properties may require additional registry-owned links. The required family is
computed from the request and its actual subject, never inferred from proof-term
usage or supplied by a proof method. Missing proofs keep the request open. The
assurance specification owns permitted assumptions and axiom checks.

### Identity, oracle operations and suites

These vocabularies remain typed and owned by their defining schemas. This
register does not merge several different identities into one untyped string:

- Written AST nodes, claim attachments, semantic source occurrences, dynamic
  loop coordinates and realization rows identify different objects. Every crossing
  needs an explicit checked association. Companion navigation keys may survive
  an edit; the exact expected Lean type and subject identity must still be checked.
- Logical oracle operation descriptors are owned by the IR/structured-source
  specification. Frontend spellings map to those descriptors, and formal readers
  reject unknown forms. Wire decoding alone does not admit oracle execution.
- Installed suites are exact catalog entries with domains, representations,
  transcript/hash/codec choices and implementation identities. Runtime availability
  does not imply formal support. In particular, the current
  [executable vocabulary](../../lean/Zkc/Executable/Installed.lean) covers selected
  BLS12-381/Merlin operations; the quartic KoalaBear flagship requires additional
  checked interpretations and cannot inherit that support by name.

The operation catalog probe must establish one law-bearing family through source
spelling, IR signature, executable binding and Lean definition before extending
it broadly. Algebraic identity, total mathematical behavior, checked execution
and native resource refusal are separate contracts, even when they share an
operation name.
