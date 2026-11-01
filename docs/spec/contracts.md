# Cross-component contract register

This register assigns one semantic owner to each shared contract and records its
producers, consumers and delivery boundary. The linked specifications own the
exact definitions. Registration is not implementation, semantic admission or a
proof. The [foundation interface inventory](formats/foundation-interfaces.md)
lists the current cutover and planned schema boundaries. All formats remain at version `0`; current
and designed schemas are distinguished by their stated support, not a version
bump. No compatibility reader is introduced.

A contract-changing PR updates its row, enumerations and affected consumers. Its
review records identify which consumer boundaries were checked and which remain
open. Each component implements its own reader; shared generation of signatures
does not replace independent interpretation or admission. The Lean component is
the sole writer of `lean/`. Native owners specify their formats in this register
and `docs/spec`; Lean adapts its readers, interpretations and exact-subject
artifacts against those landed contracts. A native landing may precede that
formal adaptation; its row must keep the missing consumer explicit. During the
native foundation, IR publishes shared contracts first; no Lean patch, handoff
or build is part of the native unit. Archived `INTERFACE.md` coordination documents are retired
as interface authorities; this register and its linked specifications replace
them.

Frontend owns the checked program and written source associations. IR owns
the shared catalog, generated registries, lowering the checked program into IR,
and comparison against the actual emitted IR. Lean owns its interpretation and
receipt audit. Consumer requirement coverage does not change an independently
valid receipt's meaning or proof status.

Compiler representation ownership follows [serialization boundaries](../compiler/serialization.md).
Native source analyses now consume retained MLIR and bounded operation views;
structured source, claims and source correspondence remain external projections.
Oracle realization checks typed proposals against actual bodies before record
publication. Upstream bytecode is accepted at the structured IR input boundary,
with exact-encoding identities and no claimed textual ranges. Canonical source
admission and all owned wire schemas remain at their current version-0 forms.
No independent formal consumer is changed by this native ownership migration.

## Contract inventory

The [interaction analysis contract](ir/interactions.md) fixes shared structural
extraction and separate judgments for dependency, exact custody, reached facts,
authentication and sampling. IR owns the borrowed native view and independent
source/candidate checks. Application maps and realization records retain their
own schemas; no additional serialized interaction program is introduced.
Native scalar observations distinguish participant-specific components from
uniform constants. Observation ordering, successful-point bounds and capacity
consume that same bounded interpretation; only exact uniform counts can tighten
repeat capacity. Request-loop obligations retain source order even when their
IR allocation order differs. These strengthen analysis and deterministic
construction without changing a serialized schema or registering a new claim.
Implementation coverage remains explicit in [status](../status.md), and formal
interpretation remains an independent consumer obligation.

The [execution observation summary](ir/execution-observations.md) is a borrowed
native analysis of actual numerical bodies, including logical stops and closed
finite callbacks. It retains exact primitive occurrences as interpretation
premises and is not a transcript-binding or security certificate. The
[structured public-coin consumer](ir/public-coin.md) selects the authored
or checked realized subject explicitly and serializes shared definition DAGs.
Its required deployment inventory and independent policies reproduce the same
checked owner as compilation. All verifier data inputs are binding obligations,
including unused and generated shape inputs. No serialized formal consumer or
Lean interpretation is claimed by this native summary.

The [protocol observation summary](ir/protocol-observations.md) composes those
numerical facts through actual Protocol definitions, role maps and retained
repeats. Its dependency DAG and exact pending-challenge transfer are distinct:
arithmetic dependence never establishes exact delivery. This is an internal
borrowed analysis, not a new artifact format or an additional execution route.

The separate [construction binding view](ir/construction-binding.md) checks
actual encoding coverage and state successors after source/candidate
correspondence. All profiles distinguish terminal event templates outside query
coverage from observations absorbed into a final history state. Primitive/codec
meaning, host initialization where applicable and cryptographic laws remain
explicit premises; the report grants no execution authority or security theorem.

### Logical collection ownership

Data is the single native MLIR owner of `field_vector`, `group_vector`,
`indices`, `field_matrix`, `field_array`, `fixed_vector`, `sequence` and `bytes`,
their structural operations and catalog type adapters. Exact-array construction
and observation, and logical finite fold/collect, use `data.*` operations. The
replaced `algebra.*` collection types and structural operations are not
registered and have no parser aliases. Algebra retains scalar fields, groups
and operations expressing algebraic meaning.

This native IR cutover preserves logical family identities, layout, custody,
admission and serialized catalog/type spellings. Equal element type and extent
do not identify different families. Native source producers, mathematical and
finite readers, computation/physical selection, EVM lowering and fixtures move
together. Structured-source, application-map and program-byte vocabulary retain
their existing family names; these formats do not serialize the MLIR namespace.
See [representation ownership](../compiler/representation.md). Independent
formal code and its native-MLIR fixtures remain owned by the Lean component.

### Represented arithmetic boundary

[Canonical Residue arithmetic](ir/residues.md) owns modular values, width and
lift laws; [Codec](realization/codecs.md) owns the exact logical/coordinate/limb/
byte relations. Nominal fields and polynomial domains keep their original
owners. The word-lowering producer retains its source and yields a private
standard-Arith candidate. The independent scalar reader checks actual ranges,
modular expressions and centered lifts, including candidates changed by CSE.
A private-tile reader additionally checks static Vector/MemRef bounds and
ownership, with peak canonical-word storage. The checked expression and storage
plan reach the CPU consumer under its resident value relation and fallible
resource scope. The dialect itself introduces no serialized representation
certificate or executable wire type; independent formal interpretation remains
separate.

### Physical numerical plans

[Physical numerical plans](runtime/numerical-plans.md) define the target-stage
`zkc.numerical-plan/0` parameter: actual Ring expression, lane bound and scratch
slot assignment. Logical parameters remain Ring expressions. The replacement
changes executable parameters, scratch admission and the setup byte term in the
numerical work score. Compiler materialization, independent C++ and Rust
readers, reached CPU consumers and fixtures use this carrier. Bare executable
Ring parameters are rejected. The compiler checks source correspondence and
the native consumer independently admits the actual schedule; native admission
does not establish a Lean interpretation or source-to-execution theorem.

### Participant-loop capture bindings

Participant `loop` captures in `zkc.program/0` are ordered
`[local_name, parent_name]` pairs. This preserves distinct Copy formals that
refer to one parent value, including their storage accounting. The compiler,
independent artifact checker, native decoder, interpreter and proof admission
readers use this form together. The old string list is rejected; local numeric
control keeps its existing grammar. See the
[byte-language change](formats/program-bytes.md#participant-bodies). This is a
version-0 schema replacement, not a compatibility profile. Independent formal
reader adaptation remains separate.

### Foundation interfaces

These rows identify the native cutover and independently maintained consumers.
All use version `0`; the change list defines the replacement schema, with no
compatibility reader. Native implementation does not establish formal support.
IR owns the catalog, lowering and
native contract changes during this unit; frontend owns the checked program.
The broad migration uses main `abe85f7a7`, which contains the frontend redesign
and native Common-export retirement. Native interface checks replace cross-session
review loops for this unit. Formal interpretation is a later independent task.

| Identifier / version | Specification and owner | Producer → consumers | Missing integration |
|---|---|---|---|
| `zkc.logical-types/0` | [Logical type data](formats/logical-types.md), IR / Contracts | Typed IR export → native artifact readers, independent semantic readers | Native structured codecs and standalone inventory API; independent semantic interpretation remains separate |
| `zkc.contract-declarations/0` | [Catalog](formats/contract-declarations.md), IR / Contracts | Neutral declarations → Language, MLIR, Rust and serialized formal-consumer data | One source generates C++/ODS, Rust and fixed consumer profiles; typed invocation/signature/parameter formation and independent runtime admission consume it; no Lean implementation in this unit |
| `zkc.structured-source/0` | [Cutover](formats/foundation-interfaces.md#structured-source), IR / Protocol | Structured exporter → independent semantic readers | Native readers validate complete structured types, bindings and parameters; the formal reader preserves logical-sort oracle descriptors and logical-record origins. New total-word meanings and oracle execution await formal interpretation |
| `zkc.constructed-participant/0`, `zkc.constructed-pair/0` | [Cutover](formats/foundation-interfaces.md#constructed-participants), IR / Construction | Actual candidate export → independent construction/projection readers | Native participant/pair producers and the formal constructor bridge use closed structured codecs; checked connection certificates establish the admitted formal profile |
| `zkc.oracle-realization/0` | [Cutover](formats/foundation-interfaces.md#realization-and-application-records), IR / Transforms | Realization producer → native actual-body reader, independent interpretation | Native structured type inventory and actual-body reader implemented; independent interpretation unsupported |
| `zkc.application-map/0` | [Application map](formats/application-map.md), IR / Transforms | Source/candidate association → native comparison, independent correspondence reader | Producer and independent actual-candidate checker implemented for unsimplified preparation; no correspondence theorem or simplified-rewrite profile implied |
| Checked selected endpoint closure | [Computation](ir/computation.md#selected-endpoint-closure), IR / Compiler | Complete constructed closed Exec → common endpoint reader → CPU physical selection and EVM legality | Both targets retain complete source correspondence separately from the selected executable inventory; each target owns its lowering and executable admission |
| `zkc.evm-source/0`, `zkc.evm-artifact/0` | [EVM target](targets/evm.md), EVM compiler and SDK | Checked verifier → legalized EVM/Yul → pinned solc → authenticated SDK artifact → deployed verifier | Shared logical layouts, prime/extension arithmetic, finite/structured transport and fork-bound options; deployed differential evidence, with cryptographic expansion and formal lowering correspondence separate |
| Outcome, stop, budget meaning | [Native foundation](ir/native-foundation.md#outcomes-observations-and-budgets), IR / Execution | Typed invocation → compiler admission and native VM/providers | Typed route implemented; existing reached schedule, stops and budgets retained |
| Native successor operands | [Execution branches](ir/execution.md#structural-branch-interfaces-and-admitted-execution), IR / Data and Exec | Native builders and source emitter → BranchOpInterface clients, source readers and correspondence checks | Independent forwarded segments implemented; generic CFG publication still requires semantic binding, custody and budget correspondence beyond structural formation |
| Stage admission and target selection | [Stage pipelines](ir/native-foundation.md#stage-pipelines-and-target-selection), IR / Compiler | Shared stage builder and selected installation → API, textual pipeline, import and publication | Shared stage builders, typed selection and complete native admission; catalog availability does not establish an installed backend |
| `zkc.program/0` | [Retained byte language](formats/foundation-interfaces.md#executable-byte-language), IR / Program | Compiler → independent C++/Rust readers and other target consumers | Logical execution retained with explicit local/parent loop-capture bindings; structural native adapter and independent byte readers use the current byte grammar |

### Current producers and consumers

`Implemented` describes the named producer/consumer profile, not all possible
consumers. `Partial` names a missing consumer or behavior. `Designed` has no
production format or admission authority. The last-PR column records the last
contract change, not the most recent documentation-only registration.

| Identifier / version | Owning specification | Single owner | Producer → consumer code | Status | Stages or links introduced | Last PR |
|---|---|---|---|---|---|---|
| `zkc.source-ast/0` | [Written source](language/source-ast.md) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → future Lean elaboration reader | Partial: both native grammars and neutral formal nodes exported; independent source reader remains open | None; does not discharge `source.correspondence` | [#186](https://github.com/zkcompiler/zkc/pull/186) |
| `zkc.source-bindings/0` | [Binding proposals](language/source-ast.md#source-binding-proposals) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: retained resolutions; no elaboration soundness theorem | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-instances/0` | [Closed instances](language/source-ast.md#closed-source-instances) | Frontend / Language | [Compiler](../../compiler/lib/Compiler) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: closed instances and mandatory unresolved oracle construction substitutions with whole-Formula lookup keys; independent source/IR occurrence association, expected-type checking and call-edge proof remain open | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-correspondence/0` | [Checked elaboration](language/elaboration.md) | Frontend / Language | [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp) → future Lean correspondence checker | Partial: producer and native association checks; proof open | Proposed source-to-admitted connection | [#185](https://github.com/zkcompiler/zkc/pull/185) |
| Structured source, version 0 | [Structured source](formats/structured-source.md) | IR / Protocol | [StructuredSource.cpp](../../compiler/lib/Compiler/StructuredSource.cpp) → [Lean structured reader](../../lean/Zkc/Source/Structured) | Partial: strict Lean type/binding/parameter reading, logical-record origins and complete oracle input/component logical sorts are installed; new total-word meanings and oracle execution remain outside the ordinary formal profile | Existing source interpretation; wire recognition grants no oracle execution admission | [#194](https://github.com/zkcompiler/zkc/pull/194) |
| Logical oracle operations and kinds, version 0 | [Protocol oracles](ir/protocols.md#logical-oracle-kinds-and-handles), [wire operations](formats/structured-source.md#logical-oracle-vocabulary) | IR / Protocol | [OracleOps.td](../../compiler/include/zkc/Dialect/Protocol/IR/OracleOps.td), [Protocol formation](../../compiler/lib/Dialect/Protocol/IR/Oracles.cpp) → [realization](../../compiler/lib/Transforms/OracleCommonRealization.cpp), frontend emission, Lean reader | Native table/virtual semantics, checked source projection and realization implemented; the independent Lean reader preserves logical-sort descriptors and sequence capacity; oracle execution still needs independent Lean interpretation | No new registered claim stage | [#194](https://github.com/zkcompiler/zkc/pull/194) |
| `zkc.oracle-obligations/0` | [Oracle proposals](formats/structured-source.md#oracle-obligation-proposals) | IR / Protocol | [OracleObligations.cpp](../../compiler/lib/Compiler/OracleObligations.cpp) → native comparison and Lean independent derivation | Partial: independently checked occurrence-bound templates and footprints; no predicate discharge | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.oracle-realization/0` | [Realization record](formats/oracle-realization.md) | IR / Transforms | [OracleRealizationRecord.cpp](../../compiler/lib/Transforms/OracleRealizationRecord.cpp) → [actual-body reader](../../compiler/lib/Transforms/OracleCommonVerification.cpp), future Lean realization reader | Native checked table and virtual queries, dynamic complete-window authentication and ordered replay implemented; Lean simulation open | Realization is a compiler boundary; `realization.correspondence` remains unregistered | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.oracle-selection/0` and requested compiler policy | [Requested selection](formats/oracle-realization.md#requested-selection) | IR / Compiler | C++ API, CLI and SDK settings → exact source-derived selection admission and packaged options | Implemented uniform/exact requests through C++/CLI/SDK, source-relative admission and mandatory packaged policy | None; selected implementation is not a binding or simulation theorem | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.constructed-participant/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.constructed-pair/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.program/0` | [Program bytes](formats/program-bytes.md) | IR / Program | [Encode.cpp](../../compiler/lib/Program/Encode.cpp) → [Decode.cpp](../../compiler/lib/Program/Decode.cpp), [native VM](../../crates/zkc-runtime/src/vm), [Lean renderer](../../lean/bridges/executable/render.py) | Partial: native readers and shared corpus; Lean installed table has a narrower profile | Input to `lowering.interpreted_bytes`; native runtime conformance separate | [#179](https://github.com/zkcompiler/zkc/pull/179) |
| Retired Common source | [Structured-source replacement](../../lean/docs/spec/structured-source.md) | Former IR / Compiler, Lean / Source | No retained producer or reader | Retired in favor of original structured source and its Domain interpretation | No additional admitted link | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.language-interface/0` | [Language interface](formats/entry.md) | Frontend / Language | [LanguageInterfaceWriter.cpp](../../compiler/lib/Compiler/LanguageInterfaceWriter.cpp) → [native comparison](../../compiler/lib/Compiler/LanguageInterfaceComparison.cpp), [Rust Host](../../crates/zkc/src/entry/interface/raw.rs), [Lean bridges](../../lean/bridges) | Partial: logical oracle alternatives are not executable Host payloads; Host refuses them | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.host/0` | [Entry Host](formats/entry.md) | IR / Translation | [Direct native emitter](../../compiler/lib/Translation/Entry/Emission.cpp) → [independent SSA artifact reader](../../compiler/lib/Translation/Entry/Reader.cpp), [Rust Host](../../crates/zkc/src/entry) | Implemented: actual Func/CF ports, layouts and outcomes determine the artifact; no retained body or signature JSON | Native source comparison only | [#187](https://github.com/zkcompiler/zkc/pull/187) |
| `zkc.run/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers and checked oracle proof publication; logical claim transport and formal realization remain open | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.entry/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers and checked oracle proof publication; logical claim transport and formal realization remain open | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.native-proof/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers and checked oracle proof publication; logical claim transport and formal realization remain open | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| Deterministic verifier-request construction, version 0 | [Request relation and target schema](ir/verifier-requests.md) | IR / Compiler | Checked realization → participant construction and independent actual-body reader → native descriptor and executable endpoint admission | Implemented checked reconstruction, reconstructed-message events, normalized selection and independent native endpoint admission; ordinary oracle/FRI proofs execute; no runtime SSA certificate carrier | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.contract-declarations/0` | [Shared catalog](formats/contract-declarations.md) | IR / Contracts | [Neutral source](../../common/catalog/README.md) → C++/ODS, [Rust metadata](../../crates/zkc-catalog/README.md) and serialized inventory; [Rust admission](../../crates/zkc-runtime/src/vm/operations/mod.rs) interprets declarations with independently owned backend installations | Partial: native and Rust projections consumed; the formal bridge decodes structural metadata and independently derives installed primitive signatures; new native operations require separately installed Lean meanings | None; signatures do not prove kernel laws | [#187](https://github.com/zkcompiler/zkc/pull/187) |
| `zkc.source-claims/0` | [Source requests](language/claims.md) | Frontend / Language | [Language SourceClaims.cpp](../../compiler/lib/Language/SourceClaims.cpp), [compiler export](../../compiler/lib/Compiler/SourceClaims.cpp) → [Lean bridges](../../lean/bridges) | Implemented original-grammar requests; new frontend integration pending | Selects an existing stage; introduces none | [#176](https://github.com/zkcompiler/zkc/pull/176) |
| `zkc.bound-source-claims/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject-evidence/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.declarations/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.assurance-report/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.consumer-requirements/0` | [Independent consumer scope](../../lean/docs/spec/assurance-report.md) | Lean / Claims, with frontend consumer integration | Independent consumer file → [record checks](../../lean/checks/check_records.py), Lean receipt audit → report consumer | Partial: independent occurrence/context input and post-audit coverage; frontend producer integration pending | Adds omission accounting; changes no receipt meaning or stage | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.companion/0` lookup identity and obligation inventory | [Companions](language/companions.md) | Frontend / Language | Authored inventory and generated lookup addresses → [Lean typed resolver](../../lean/ZkcTools/Companions.lean) and [assembly](../../lean/ZkcTools/Companions/Assembly.lean) | Partial: lookup keys, mandatory pending postconditions and native whole-Formula oracle-admissibility addresses implemented. Oracle occurrence substitutions remain unresolved; independent source/IR association, oracle expected-type checking and proof discharge remain open. Existing Lean typed resolution/assembly and retained Entry-origin/closed-instance lookup are installed within their profile; intermediate source spans remain open | None; existing Lean admission remains authority | [#185](https://github.com/zkcompiler/zkc/pull/185) |
| Layout requests and authored site selection | [Layout syntax](language/layout-syntax.md), [site defaults](language/layout-execution.md) | Frontend / Language | Lossless syntax and native projection → written occurrences and pending obligations | Partial: source association retained; typed request generation and independent checking pending | Selects existing meanings; adds no assurance stage | [#186](https://github.com/zkcompiler/zkc/pull/186) |
| Retired proposal `zkc.lean-interface/0` | [Shared interfaces plan](../roadmap.md#shared-interfaces-before-implementation) | Frontend / Language | Existing declarations and bound requests → frontend resolution | Retired proposal: extend existing transports; no parallel format is admitted | None | — |
| Restricted logical aggregates; version unassigned | [Logical aggregate plan](../roadmap.md#shared-interfaces-before-implementation) | IR / Protocol | Future frontend claim views → Protocol formation and Lean reader | Designed: typed field paths and role components; ordinary data/codec boundaries continue to exclude handles | None | — |
| Native index blocks and gated requests, version 0 | [Request bytes](formats/native-index-block.md), [construction](ir/construction.md#native-index-blocks) | IR / Construction | Native construction → independent actual-body and Rust readers, CPU bounded search/check, SDK transport | Native compiler/runtime integration; independent Lean adaptation remains open | No registered gate premise or Fiat–Shamir theorem | — |
| `zkc.construction-binding/0` | [Closed binding profiles](ir/construction-binding.md) | IR / Compiler | Actual original/candidate correspondence → canonical encoding/state analysis → complete recomputation | Native history, canonical hash history and explicit-input coverage; bounded closed profiles | Primitive interpretation, host initialization and cryptographic premises remain explicit; not a security theorem | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Source-selected gates, version 0 | [Proof choices](language/entries.md#proof-declarations), [written syntax](language/source-ast.md) | Frontend / IR | Checked labelled query paths → source/interface comparison, native selection and SDK artifact binding | Required `gates` proof-job field and written `gate` nodes; native policy and witness wire unchanged | Direct installed block construction only; no security theorem from difficulty | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Expanded local occurrence names | [Function origins](ir/functions.md#origins-and-identity), IR / Algorithms | Scoped expansion and numerical realization → independent correspondence readers and emitted native sites | Full length-delimited paths remain in origin records; long names use the complete SHA-256 digest in unpadded base64url; native producers and checkers change together | Names do not establish correspondence; independent formal consumers are not migrated here | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| CPU retained-value profile | [Native capacity](runtime/capacity.md#retained-values-and-logical-work), Runtime / CPU | CPU value constructors, preflight and codecs → VM retention and shared execution ledgers | 80-byte inline slots; large group points, complete variant nodes and aggregate metadata use charged immutable backing; expanded value bounds and live capability validation remain independent | Native resource accounting only; no new formal claim | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| Parameterized STARK degree reduction | [Assignment inventory and DEEP contract](domains/stark.md) | Libraries / IR | Captured Bundle → extended OOD inventory → adjusted first FRI word and authenticated query association | Implemented native profile; degree-boundary adversary, full-column inventory and scalar/product/gated quartic Keccak deployments exercised | No complete DEEP/FRI, commitment or FS theorem for this compiled client | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Installed transcript and Merkle suites | [Transcripts](ir/construction.md), [Merkle schemes](domains/oracles.md), [services](runtime/services.md) | Runtime / Providers | [Backend registry](../../crates/zkc-cpu/src/backend/registry.rs) → Contracts selection, native invocation, Lean installed vocabulary | Native quartic Keccak rows, randomness and hash-chain transcript installed; independent Lean coverage remains separate | Kernel interpretation remains explicit | [#174](https://github.com/zkcompiler/zkc/pull/174) |

For designed rows, the linked roadmap is a delivery contract, not a wire
specification. Their owner supplies a repository specification and code paths
before a producer and consumer can claim interoperability. A private proposal
or a branch-local implementation cannot silently register an accepted value.

The layout frontend's explicit role assembly is governed by
[layout execution](language/layout-execution.md) and the existing
[IR assembly contract](ir/protocols.md). Frontend owns parsing, checked types and
placement, and written component order. IR owns lowering, formation, participant
projection and actual-IR comparison. The source AST retains ordered assembly
components without an equality premise or a new claim stage. The independent
Lean source checker must check the same selection.

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
operation to every target. Catalog changes at the
[foundation regression boundary](../roadmap.md#preserve-the-landed-foundation)
account for frontend, ODS, native execution and independent Lean vocabulary
consumers. Declaration agreement does not establish their semantic interpretation.

The proposed standalone `zkc.lean-interface/0` is superseded by projections
of existing Lean declarations, subjects and bound-request formats. The
[frontend architecture](../compiler/frontend-architecture.md) records the
source resolution boundary; no second proof pipeline is introduced.

## Formal assurance boundary

The installed infrastructure link families are defined in
[StageLinks](../../lean/security/ZkcSecurity/Claims/StageLinks.lean),
[DomainSubject](../../lean/security/ZkcSecurity/Bindings/Subjects/Domain.lean) and
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

The [IR-relative assurance scope](../assurance.md#ir-relative-security-claims)
names frontend elaboration as trusted. Independent source elaboration is a
stronger assurance target, not a prerequisite for that scope. This changes no
registered link, stage or receipt rule. In particular, checked connections for
security-changing construction and realization remain required when claimed.

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

### Required checked edges

An identity always includes its enclosing immutable artifact. Similar printed
names from different domains are not interchangeable.

| Domain | Anchor | Checked edge to the next domain |
| --- | --- | --- |
| Written node | `(capture, installation, owner, path)` in `zkc.source-ast/0` | Elaboration reader validates name resolution, binders, role substitution and lowering against the admitted program. |
| Authored/inferred site | Declaration instance plus site label and nesting/call route | Native occurrence export selects actual operations. Explicit labels and default names obey one uniqueness rule. |
| Closed declaration instance | Template plus checked, ordered static substitution under the installation | `zkc.source-instances/0` associates the instance with the structured admitted symbol. Printed symbols alone prove nothing. |
| Structured row | Exact snapshot/admission plus row | Actual-module reader checks ports, operations, ordering and origin associations. |
| Native execution origin | Complete `native-origin/0` origin under the selected program | The transcript/observation contract checks exact encoding and reached occurrence; an AST path cannot substitute for its bytes. |
| Obligation key | Source/instance identity plus semantic role and local key | Companion matching checks the independently fixed Lean type; a key is a lookup address, not a proof digest. |
| Realization occurrence | Exact original/realized artifacts plus occurrence selection | IR realization reader checks the actual selected operations and ordered expansion; Lean separately proves the realization link. |
| Bound request | Exact subject, admitted request digest and source attachment | Receipt audit compares the admitted request, dependency scope and required consumer set with receipts. |

Source insertion can change ordinal paths. Renaming a default site changes its
site identity. A stable explicit label does not preserve a proof across changed
program semantics: artifact identity and the fixed expected proposition still
change. No mapping above is inferred from equal spans or string prefixes.

## Shared oracle-stack acceptance boundary

The native [query-batch record](formats/oracle-realization.md#checked-query-batches)
uses the single `/0` helper inventory including mandatory `check_available`.
The compiler producer and exact record reader migrate together. Independent
batch and complete Common readers check demand/store-only collection and the
verifier's actual zero-result empty-prefix check before grouping or exchange.
The [request reconstruction contract](ir/verifier-requests.md) continues to
require complete needed Local calls; this boundary split grants no partial-call
pruning and changes no runtime carrier or independent formal model.

The common acceptance client is FRI/STARK written in the agreed frontend
language, using KoalaBear with its quartic extension and Keccak Merkle rows.
This is a cross-component completion test; the Merkle query landing alone does
not pass it.

- Frontend spells all twelve logical operations, restricted logical claim
  aggregates, setup authority and explicit realization selection. Its written
  source export must preserve source associations through elaboration.
  The current [layout oracle profile](language/oracles.md) includes checked
  virtual definitions and restricted logical records. Logical external Host
  ports and source-written deployment selection remain outside that profile.
- IR preserves anchors, holder/receiver custody, named shapes, ordered domain
  failures, virtual dependencies and complete realization records. Dynamic
  complete-window authentication and ordered replay serve the shared FRI source;
  the separate fixed-query route is removed. IR owns the index vocabulary, application
  correspondence format and catalog projection schema; Lean interprets their
  landed specifications independently.
- Lean reads the exact logical wire vocabulary and independently derives oracle
  obligation proposals. Recursive handle exclusion keeps these outside ordinary
  execution and data codecs. Oracle execution, realization-stage/link registration,
  independent realization-record interpretation and its simulation remain open.
  Unknown profiles remain refused.
- Runtime installs quartic Keccak rows, its randomness service and hash-chain
  transcript. A compiled row-opening proof has native/browser byte agreement;
  this does not establish the shared FRI/STARK client. Explicit native index-block
  policies emit bounded prover search, a construction-owned witness slot and the
  verifier gate check. Independent readers check actual helper/transport order;
  CPU checks bytes, authority, accounting and failure successors. Source proof
  declarations select gates by checked labelled query paths; Lean interpretation remains open.
  An installed signature alone does not prove its implementation.

Report these four results separately against the same source and configuration.
The same logical client under ideal, Poseidon2-Merkle and Keccak-Merkle choices
must retain its protocol meaning; neither matching successful outputs nor a
single passing implementation establishes cryptographic or resource equivalence.

The runtime owns the SDK source-format cutover. Frontend syntax support does
not switch production defaults. The source/request connection and host/editor
consumers must satisfy their owning contracts before that switch.

The scalar-selection addition keeps the current `/0` declaration and program
formats: four exact operation rows (`bool.select`, `index.select`,
`field.select<F>`, `curve.select<G>`) implement the existing mathematical
`arith.select` profile. Catalog projections, native installation, independent
recipe readback and CPU advertisement change together. See [value meanings](domains/values.md#total-scalar-selection)
and [mathematical realization](ir/mathematics.md#scalar-selection-realization).
Independent formal consumer admission is not enlarged by these native rows.
