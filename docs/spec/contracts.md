# Cross-component contract register

This register assigns one semantic owner to each shared contract and records its
producers, consumers and delivery boundary. The linked specifications own the
exact definitions. Registration is not implementation, semantic admission or a
proof. Version `0` denotes the current schema, with no compatibility reader.

A contract-changing PR updates its row, enumerations and affected consumers. Its
review records identify which consumer boundaries were checked and which remain
open. Each component implements its own reader; shared generation of signatures
does not replace independent interpretation or admission. The Lean component is
the sole writer of `lean/`; changes proposed elsewhere are supplied for that
owner to integrate. Archived `INTERFACE.md` coordination documents are retired
as interface authorities; this register and its linked specifications replace
them.

## Contract inventory

`Implemented` describes the named producer/consumer profile, not all possible
consumers. `Partial` names a missing consumer or behavior. `Designed` has no
production format or admission authority. The last-PR column records the last
contract change, not the most recent documentation-only registration.

| Identifier / version | Owning specification | Single owner | Producer → consumer code | Status | Stages or links introduced | Last PR |
|---|---|---|---|---|---|---|
| `zkc.source-ast/0` | [Written source](language/source-ast.md) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → future Lean elaboration reader | Partial: original syntax and stable node paths exported; independent source reader remains open | None; does not discharge `source.correspondence` | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.source-bindings/0` | [Binding proposals](language/source-ast.md#source-binding-proposals) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: retained resolutions; no elaboration soundness theorem | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-instances/0` | [Closed instances](language/source-ast.md#closed-source-instances) | Frontend / Language | [Compiler](../../compiler/lib/Compiler) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: closed instance associations; call-edge proof open | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-correspondence/0` | [Elaboration associations](language/source-ast.md#checked-source-artifact) | Frontend / Language | [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp) → future Lean correspondence checker | Partial: producer and native association checks; proof open | Proposed source-to-admitted connection | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| Structured source, version 0 | [Structured source](formats/structured-source.md) | IR / Protocol | [StructuredSource.cpp](../../compiler/lib/Compiler/StructuredSource.cpp) → [Lean structured reader](../../lean/Zkc/Source/Structured) | Partial: native oracle/assemble vocabulary; Lean integration pending | Existing source interpretation; no oracle execution admission | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| Logical oracle operations and kinds, version 0 | [Protocol oracles](ir/protocols.md#logical-oracle-kinds-and-handles), [wire operations](formats/structured-source.md#logical-oracle-vocabulary) | IR / Protocol | [OracleOps.td](../../compiler/include/zkc/Dialect/Protocol/IR/OracleOps.td), [Protocol formation](../../compiler/lib/Dialect/Protocol/IR/Oracles.cpp) → [realization](../../compiler/lib/Transforms/OracleCommonRealization.cpp), frontend emission, Lean reader | Partial: native table/virtual semantics and realization; full frontend spelling and Lean semantics pending | No new registered claim stage | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.oracle-obligations/0` | [Oracle proposals](formats/structured-source.md#oracle-obligation-proposals) | IR / Protocol | [OracleObligations.cpp](../../compiler/lib/Compiler/OracleObligations.cpp) → native comparison; Lean independent derivation pending integration | Partial: occurrence-bound templates and footprints; no predicate discharge | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.oracle-realization/0` | [Realization record](formats/oracle-realization.md) | IR / Transforms | [OracleRealizationRecord.cpp](../../compiler/lib/Transforms/OracleRealizationRecord.cpp) → [actual-body reader](../../compiler/lib/Transforms/OracleCommonVerification.cpp), future Lean realization reader | Partial: native checked table queries and fixed base-query blocks; Lean simulation open | Realization is a compiler boundary; `realization.correspondence` remains unregistered | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| Realization selection, C++ API | [Requested policy](formats/oracle-realization.md#json-envelope-and-limits) | IR / Compiler | [RunOptions](../../compiler/include/zkc/Compiler/Run.h) → [selection admission](../../compiler/lib/Transforms/OracleRealizationSelection.cpp) | Partial: explicit C++ policy; frontend/CLI/SDK producer pending | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.constructed-participant/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.constructed-pair/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.program/0` | [Program bytes](formats/program-bytes.md) | IR / Program | [Encode.cpp](../../compiler/lib/Program/Encode.cpp) → [Decode.cpp](../../compiler/lib/Program/Decode.cpp), [native VM](../../crates/zkc-runtime/src/vm), [Lean renderer](../../lean/bridges/executable/render.py) | Partial: native readers and shared corpus; Lean installed table has a narrower profile | Input to `lowering.interpreted_bytes`; native runtime conformance separate | [#179](https://github.com/zkcompiler/zkc/pull/179) |
| Retired Common source | [Structured-source replacement](../../lean/docs/spec/structured-source.md) | Former IR / Compiler, Lean / Source | No retained producer or reader | Retired in favor of original structured source and its Domain interpretation | No additional admitted link | — |
| `zkc.language-interface/0` | [Language interface](formats/entry.md) | Frontend / Language | [LanguageInterfaceWriter.cpp](../../compiler/lib/Compiler/LanguageInterfaceWriter.cpp) → [native comparison](../../compiler/lib/Compiler/LanguageInterfaceComparison.cpp), [Rust Host](../../crates/zkc/src/entry/interface/raw.rs), [Lean bridges](../../lean/bridges) | Partial: logical oracle alternatives are not executable Host payloads; Host refuses them | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.run/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers; logical oracle proof publication remains open | No new assurance stage | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.entry/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers; logical oracle proof publication remains open | No new assurance stage | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.native-proof/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers; logical oracle proof publication remains open | No new assurance stage | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.contract-declarations/0` | [Operation contracts](../compiler/operation-contracts.md) | IR / Contracts | [Neutral declarations](../../compiler/include/zkc/Contracts/Declarations) → C++ adapters, [Rust registry](../../crates/zkc-cpu/src/backend/registry.rs), [Lean installed vocabulary](../../lean/Zkc/Executable/Installed.lean) | Partial: C++ generated; Rust/Lean tables independently maintained, with different coverage | None; signatures do not prove kernel laws | [#170](https://github.com/zkcompiler/zkc/pull/170) |
| `zkc.source-claims/0` | [Source requests](language/claims.md) | Frontend / Language | [Language SourceClaims.cpp](../../compiler/lib/Language/SourceClaims.cpp), [compiler export](../../compiler/lib/Compiler/SourceClaims.cpp) → [Lean bridges](../../lean/bridges) | Implemented original-grammar requests; new frontend integration pending | Selects an existing stage; introduces none | [#176](https://github.com/zkcompiler/zkc/pull/176) |
| `zkc.bound-source-claims/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject-evidence/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.declarations/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.assurance-report/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.consumer-requirements/0` | [Independent consumer scope](../../lean/docs/spec/assurance-report.md) | Lean / Claims, with frontend consumer integration | Independent consumer file → [record checks](../../lean/checks/check_records.py), Lean receipt audit → report consumer | Partial: independent occurrence/context input and post-audit coverage; frontend producer integration pending | Adds omission accounting; changes no receipt meaning or stage | — |
| Companion / assembly contract; version unassigned | [Planned source connection](../roadmap.md#shared-interfaces-before-implementation), [existing request semantics](language/claims.md) | Frontend / Language | Future frontend module producer → [typed resolver](../../lean/ZkcTools/Companions.lean), [assembly](../../lean/ZkcTools/Companions/Assembly.lean) and existing receipt audit | Partial: typed resolver and assembly implemented; compact companion identity proposed by frontend fits resolver; source/instance producer association remains pending | None; not a second receipt authority | — |
| Retired proposal `zkc.lean-interface/0` | [Shared interfaces plan](../roadmap.md#shared-interfaces-before-implementation) | Frontend / Language | Existing declarations and bound requests → frontend resolution | Retired proposal: extend existing transports; no parallel format is admitted | None | — |
| Restricted logical aggregates; version unassigned | [Logical aggregate plan](../roadmap.md#shared-interfaces-before-implementation) | IR / Protocol | Future frontend claim views → Protocol formation and Lean reader | Designed: typed field paths and role components; ordinary data/codec boundaries continue to exclude handles | None | — |
| Application correspondence map; version unassigned | [Correspondence plan](../roadmap.md#shared-interfaces-before-implementation) | IR / Protocol | Future compiler proposal → Lean source connection checker | Designed: shared format and arbitrary relocation proof open | No new trusted link; proposals must be checked | — |
| Block/gated request wire; version unassigned | [Block requests and gating](../roadmap.md#block-requests-and-gating), [current transcript bytes](ir/construction.md) | IR / Construction | Future construction emission → runtime kernel and Lean simulation | Designed: request bytes, refusal state and accounting require joint review before installation | No registered gate premise | — |
| Installed transcript and Merkle suites | [Transcripts](ir/construction.md), [Merkle schemes](domains/oracles.md), [services](runtime/services.md) | Runtime / Providers | [Backend registry](../../crates/zkc-cpu/src/backend/registry.rs) → Contracts selection, native invocation, Lean installed vocabulary | Partial: installed native instances are explicit; flagship quartic Keccak and Lean coverage pending | Kernel interpretation remains explicit | [#174](https://github.com/zkcompiler/zkc/pull/174) |

For designed rows, the linked roadmap is a delivery contract, not a wire
specification. Their owner supplies a repository specification and code paths
before a producer and consumer can claim interoperability. A private proposal
or a branch-local implementation cannot silently register an accepted value.

## Registered enumerations

| Enumeration | Owner and authority | Accepted values / scope |
|---|---|---|
| Assurance request status | Lean / [report contract](../../lean/docs/spec/assurance-report.md) | `incomplete`, `open`, `certified`, `transport-failure`; `no-claim` denotes no canonical security claim with no unresolved consumer requirement; successful author-only coverage stays separate |
| Assurance outcome | Lean / [report contract](../../lean/docs/spec/assurance-report.md) | `established`, `unresolved` |
| Attempt results and transport envelopes | Their existing producer; [report distinction](../../lean/docs/spec/assurance-report.md) | Attempt `unsupported`, `timeout`, `refused` are not assurance states. Frontend worker/availability words require an explicit mapping; no automatic success conversion |
| Claim stages | Lean / [Stage](../../lean/Zkc/Claims/Wire.lean) | `interactive`, `compiled-ideal`, `executable-bytes` |
| Required checked links | Lean / [interpreted-stage links](../../lean/docs/spec/assurance-report.md#required-interpreted-stage-links) | Compiled validator: `construction.checked`, `construction.source_connection`; additionally `lowering.interpreted_bytes` for executable bytes. Honest pair: `pair.checked`, `pair.source`, `construction.checked`, `pair.occurrences`, `pair.producer_connection`, `pair.validator_connection`. Property-specific registry links also apply |
| Trusted source link | Lean / [Receipt](../../lean/Zkc/Claims/Receipt.lean) | `source.correspondence`, version 0; this is a remaining assumption, not a proved bridge |
| Proposed realization link | Lean / [realization connection plan](../roadmap.md#shared-interfaces-before-implementation) | `realization.correspondence` is reserved design terminology only: **not an admitted premise or stage** |
| Logical oracle operations | IR / [exact descriptors](formats/structured-source.md#logical-oracle-vocabulary) | `oracle_input`, `oracle_send`, `oracle_query`, `oracle_contents`, `oracle_components`, `oracle_shape`, `oracle_forget_shape`, `oracle_virtual`, `oracle_sequence_empty`, `oracle_sequence_append`, `oracle_sequence_at`, `oracle_sequence_length` |
| Oracle kinds and shape names | IR / [kind contract](ir/protocols.md#logical-oracle-kinds-and-handles) | Current realized kind `table`, dimension `rows`; future evaluation kinds require their own named shape schema |
| Installed suites and operations | Runtime / [suite tables](ir/construction.md), [Merkle instance tables](domains/oracles.md), [registry](../../crates/zkc-cpu/src/backend/registry.rs) | Exact identifiers and capabilities are defined there, not inferred from a field name or another suite's codec. Generated declarations and independent installed readers must agree |

The enumeration authorities above retain their definitions. This register does
not create a second runtime registry or grant every registered mathematical
operation to every target. The four-face catalog probe in the
[foundation plan](../roadmap.md#catalog-and-mlir-foundation-probe) must account for
frontend, ODS, native execution and the Lean installed vocabulary together.

## Formal assurance boundary

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

An independently supplied required occurrence/request set is compared after fresh
receipt audits, under its exact subject, manifest and checker context. Matching
display labels or method provenance cannot discharge another requirement. Missing
required work keeps coverage open without demoting valid receipt rows. Author and
generic receipts may cover explicit authoring requirements without creating a
canonical security headline. The consumer owns its required set: this check cannot
prove the set exhaustive.

## Occurrence identity

These carriers have distinct purposes. Their current names are registered here;
no common spelling establishes equality between them.

| Identity | Owner | Existing meaning and connection |
|---|---|---|
| Written `{owner, path}` | Frontend | [AST node path](language/source-ast.md); associations identify the corresponding structured rows when available |
| Structured instruction row | IR / Protocol | [Structured snapshot](formats/structured-source.md); includes exact nesting and operand references |
| `zkc.native-origin-template/0`, `zkc.native-origin/0` | IR / Construction | [Logical event path and actual repeat coordinates](ir/construction.md); native-origin bytes enter the transcript and cannot be changed for display convenience |
| Oracle obligation instruction path | IR / Protocol | [Proposal path](formats/structured-source.md#oracle-obligation-proposals), relative to the original structured snapshot |
| Realization `{entry, path}` | IR / Transforms | [Prepared instruction ordinals](formats/oracle-realization.md); source/candidate digests bind the record; not an AST or JSON-array address |
| Claim attachment | Frontend | [Request owner/block/claim occurrence](language/claims.md), joined to Lean's actual admitted subject |
| Frontend authored site and Lean invocation coordinates | Respective frontend and Lean owners | Proposed authored site selection and [formal component coordinates](../../lean/docs/spec/components.md) require a checked association to the actual source; no interchangeable string convention |

The intended path is written site → structured application path → participant
instruction → executable bytes. The application-map design must retain role maps,
arguments/results, nesting and exact source/candidate subjects. It is an
untrusted proposal consumed by Lean, not proof authority carried on an IR value.
A relocation changes the checked association even when a display label stays
unchanged. Digest spellings retain each owning format's exact grammar.

## Shared oracle-stack acceptance boundary

The common acceptance client is FRI/STARK written in the agreed frontend
language, using KoalaBear with its quartic extension and Keccak Merkle rows.
This is a cross-component completion test; the Merkle query landing alone does
not pass it.

- Frontend spells all twelve logical operations, restricted logical claim
  aggregates, setup authority and explicit realization selection. Its written
  source export must preserve source associations through elaboration.
- IR preserves anchors, holder/receiver custody, named shapes, ordered domain
  failures, virtual dependencies and complete realization records. Fixed base
  query blocks are implemented; dynamic virtual blocks and FRI index maps are
  the next delivery unit.
- Lean integrates the logical wire reader and recursive handle exclusion, then
  owns oracle execution, realization-stage/link registration, independent record
  interpretation and the required simulation. Unknown profiles remain refused.
- Runtime installs quartic Keccak rows and the agreed grinding operation, and
  validates actual request bytes, authority, resource accounting and failure
  successors. An installed signature alone does not prove its implementation.

Report these four results separately against the same source and configuration.
The same logical client under ideal, Poseidon2-Merkle and Keccak-Merkle choices
must retain its protocol meaning; neither matching successful outputs nor a
single passing implementation establishes cryptographic or resource equivalence.
