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
does not replace independent interpretation or admission. The formal component
owns the readers, interpretations and exact-subject artifacts under `lean/`;
native owners specify their formats here and in `docs/spec`. A native landing
may precede formal adaptation if its row keeps the missing consumer explicit.
Changes to the formal component require affected formal validation; an
integration that changes both sides checks both against the same contracts.
Archived `INTERFACE.md` coordination documents are retired as interface
authorities; this register and its linked specifications replace them.

Frontend owns the checked program and written source associations. IR owns
the shared catalog, generated registries, lowering the checked program into IR,
and comparison against the actual emitted IR. Lean owns its interpretation and
receipt audit. Consumer requirement coverage does not change an independently
valid receipt's meaning or proof status.

Compiler representation ownership follows [serialization boundaries](../compiler/serialization.md).
Native source analyses consume retained MLIR and bounded operation views;
structured source, claims and source correspondence remain external projections.
Oracle realization checks typed proposals against actual bodies before record
publication. Upstream bytecode is accepted at the structured IR input boundary,
with exact-encoding identities and no claimed textual ranges. Canonical source
admission and all owned wire schemas remain at their current version-0 forms.
No independent formal consumer is changed by this native ownership migration.

## Contract inventory

The [distributed record source contract](language/records.md) extends checked
Language signatures and written type nodes with ordered role applications and
recursive field placements. The source producer retains private/empty fields
and recomputes placed identities after static specialization. Native component
lowering, interface/SDK readers and independent formal interpretation remain
migration consumers; this source subunit does not establish complete native
support or introduce a compatibility schema.

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

Selected participant Program control reuses the existing `if`/`match` records
with participant bodies, typed closed captures and all-arm admission. Native
origin templates retain `["branch", original_protocol, original_branch_site,
alternative]` lexical steps, with dynamic coordinates only for repeats. The
[Program byte grammar](formats/program-bytes.md) owns their exact shapes; the
[joint schedule](runtime/joint.md#selected-participant-branches) owns strict arm
coverage, reached selector agreement and actual arm occurrence paths. C++ Program
admission and Rust VM/schedule admission are independent consumers. Native
projection, Program production and source common-input requirement binding are
integrated; the explicit
[fresh-compiler pairing gates](../../common/tests/README.md#fresh-compiler-pairing)
execute compiled packages. The [formal reader status](#formal-reader-status)
records the independent formal interpretation. Native proof construction,
request planning, codec emission and oracle realization planning have no
conditional correspondence for selected control: each refuses selected control
reachable from the selected entry's static closure, with
`native-proof-control-profile`, `native-request-control-profile`,
`native-codec-control-profile` and `oracle-realization-control-profile`
respectively. The IR session's selected-control-on-the-proof-path package
receives that feature.

The explicit [trusted input-binding context](formats/input-bindings.md) binds
an independently derived exact component inventory and actual canonical values
to externally pinned Program/entry context. Runtime owns pin/observation checking;
source/interface owns requirement derivation and flat-component mapping. No
context author supplies its own agreement certificate, and source-certified
independent execution remains gated on that complete adapter.
Value, tag and exact-axis extent observations are distinct. The SDK derives owner-associated requirements from the required per-Protocol
`common_input_requirements` member through the existing schema/component map.
`InputBoundBackendRun::start_role` checks actual inputs before creating a Runner;
`InputBoundRunEntry::prepare` checks all prepared joint data before issuance.
Compiler completeness/comparison and fresh paired publication remain producer
gates; hashing an edited package supplies no independent source-coverage claim.

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

### Participant control capture bindings

Participant `loop`, `if` and `match` captures in `zkc.program/0` are ordered
`[local_name, parent_name]` pairs. Expanding protocol applications into
participant bodies can bind two formals to one parent value; the pairs preserve
those distinct Copy formals and their storage accounting. The compiler,
independent artifact checker, native decoder, interpreter and proof admission
readers use this form together, decoding `if` and `match` by body kind. A
participant string list is rejected; local numeric control keeps its name lists,
because scoped local regions canonicalize aliased captures before emission. See
the [byte-language change](formats/program-bytes.md#participant-bodies). This is
a version-0 schema replacement, not a compatibility profile. Independent formal
reader adaptation remains separate.

### Formal reader status

Native landings precede formal adaptation, so this section keeps each missing
formal consumer explicit for the contracts changed by the STARK reduction
unit, represented execution and the frontend foundation. It records what the
current Lean-owned readers do with current native output: refuse it with a
diagnostic, fail without one, or ignore it. Lean owns every repair under
`lean/` and adapts against these landed contracts at its own sync points;
native publication does not wait for that adaptation.

| Native change | Lean-owned reader | Current behaviour |
|---|---|---|
| Participant `loop` capture rows `[local, parent]` | [Executable renderer](../../lean/bridges/executable/render.py), [executable carrier](../../lean/Zkc/Executable/Program.lean) | Read, executed and lowered: each formal is bound to its parent's value. The constructed lowering refuses a loop capture of the transcript or of a custody unit |
| Participant `if` and `match` with capture rows | Executable renderer, [execution](../../lean/Zkc/Executable/Execution.lean) | Read, including functions called only from an arm. `if` runs its selected arm in a branch frame; `match` stops as unsupported (`participant-match`). The constructed lowering refuses both (`participant-branch`) |
| Four-field `branch` origin steps | [Origin renderer](../../lean/bridges/common/lean_render.py), [schema reader](../../lean/bridges/common/schema.py), [construction steps](../../lean/Zkc/Construction/Participant.lean) | Read: a construction step is `apply`, `repeat` or a four-field `branch`, distinct from the runtime's branch frame. Source resolution and the occurrence rules refuse branch paths |
| `zkc.numerical-plan/0` executable parameters | [Numerical decoder](../../lean/Zkc/Executable/Numerical.lean) | Read: canonical plans, exact field/mask, reachability, slot layout and the invariant/varying schedule are checked. The decoder retains schedule equations used by `Schedule.run_correct`; bare ring parameters refuse. Public-module reduction and exact decimal size accounting have kernel controls; decoding alone does not establish native execution correspondence |
| Custody operations inside constructed participants | [Construction resolution](../../lean/Zkc/Construction/Participant.lean), [scalar encoding](../../lean/Zkc/Construction/Encoding.lean), [local execution](../../lean/docs/spec/executable.md) | Local typed helper and repeat frames carry exact-slot custody coordinates under the closed interpretation: create and pass return token zero; consume returns no value. Missing local custody remains incomplete, and wire payloads exclude it. Standalone participant transfers refuse (`resource_unit`). These connection laws do not establish runtime ledger freshness or nested-frame ownership |
| Installed operations without a constructed instruction | Constructed lowering | Refused: a fresh GKR program renders, and lowering refuses at `bool.not` |
| Data collection spellings in retained fixtures | [Structured fixtures](../../lean/bridges/structured/fixtures) | Retained fixtures and bridge scripts use the current collection spellings. Fresh-output comparison checks the retained exports; each textual mutation must apply once and change the text |
| Structured `data_branch`, `protocol_branch` and `variant.make` | [Structured format reader](../../lean/Zkc/Source/Structured/Format.lean) | Refused: `structured-operation-unsupported`, or `structured-list-limit` for three or more arms |
| Multi-alternative variant types | Structured format reader | Refused: `structured-type-unsupported` |
| Structured-source protocol rosters of 17 to 1,024 roles | [Structured format reader](../../lean/Zkc/Source/Structured/Format.lean), [protocol admission](../../lean/Zkc/Source/Structured/ProtocolAdmission.lean) | Read and admitted: the 1,024-role bound applies to rosters, scopes and instruction role lists, including downstream semantic admission. Record telescopes use their separate 1,024-role bound. The 1 MiB native publication ceiling is independent |
| Retained source declarations | [Declaration reader](../../lean/Zkc/Source/Structured/SourceDeclarations.lean), [component admission](../../lean/Zkc/Source/Structured/ComponentDeclarations.lean), [snapshot renderer](../../lean/bridges/structured/snapshot.py) | Read: only the current three-table carrier, including ordered telescopes, placement trees, explicit custody slots, variants and exact authority coverage. Admission checks ordinary record layouts and declared slot associations, including helper-local resources. Distributed records and variants remain named semantic refusals. Authority revisions are not recomputed from source bytes. Retained artifacts are refreshed at the integration publication boundary |
| Nonempty proof-policy gates and named construction profiles | [Construction renderer](../../lean/bridges/construction/render.py) | Refused: `unsupported policy gates`, `unsupported construction profile` |
| Constructed-participant catalogue slot | [Construction renderer](../../lean/bridges/construction/render.py), [catalogue admission](../../lean/Zkc/Construction/CatalogueAdmission.lean) | Read: binding members, capability facts and sampled service fields come from the exported rows, and `Participant.checkCatalogue` admits them against `constructionCatalogue`. Identities outside it, including the BabyBear, Goldilocks, Ristretto, BN254 and binary rows and every transcript suite other than `merlin3.bls12-381.fr64be/0` and `merlin3.koala-bear.ext8-binomial3.rejection31le/0`, refuse with `structured-catalogue-unknown`. The subject driver regenerates retained constructed-participant modules with this slot and checks their freshness against current exports |
| Shared program byte corpus | [Corpus check](../../lean/bridges/executable/corpus.py), [program admission](../../lean/Zkc/Executable/ProgramAdmission.lean) | Differential: every case is decoded natively, rendered and checked by `ProgramArtifact.admit`, and admission decisions agree; cases outside the Lean profile are listed. The check has no soundness theorem and is not an independent Lean byte reader |

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
| `zkc.contract-declarations/0` | [Catalog](formats/contract-declarations.md), IR / Contracts | Neutral declarations → Language, MLIR, Rust and serialized formal-consumer data | One source generates C++/ODS, Rust, fixed consumer profiles, installed source declarations with explicit `prelude` scope membership, notations with their rule shapes, nominal service-method identities and constructor ownership, and constructor homes; typed invocation/signature/parameter formation and independent runtime admission consume it; formal interpretations remain independently owned. The [installed-instance tables](formats/contract-declarations.md#installed-instances) (domains with field, transcript and commitment facts, logical types, frame tags, codecs, aggregate frames, random services, limits, source vocabulary) and the `Succession` facet are validated by all three generators and generated into C++ and Rust tables. The C++ owners are built from them, and the C++ consumers read them: services, message atoms, coset conventions and widths, EVM transcript suites and wire frames, the `Succession` facet, the source vocabulary and type columns, and the `protocol.roles` limit. The Rust runtime, CPU backend and SDK read them too: domain facts, logical types, codecs and frame tags, message atoms, random services and their method gates, parameter bounds, constructor facts, suites, the `protocol.roles` limit and EVM suite facts; their Rust names of domains, constructors, representations and services are bindings to catalog rows. The independent Lean Python installed-catalogue reader strictly validates the source service rows and selects `service.random` ownership; its generated Lean facts are unchanged by this schema migration. Indexed source member installation and exact query witnesses reconstruct the authored constructor, provider, request, lexical root and region; no new formal service law is claimed |
| `zkc.native-installation/0` | [Native installation](formats/native-installation.md), Runtime / native installation | Physical installation source, packaged with the declarations → C++ Contracts and CPU target, `zkc-runtime`, zkc-cpu | Validated by all three generators against its declaration package and generated into C++ and Rust tables. C++ Contracts and the CPU target read its representations, resident rows, providers, units, dense calling conventions, field forms and physical-argument convention; `zkc-runtime` and zkc-cpu read its default and alternative representations, providers, field forms and physical-argument convention, and actual target support remains each target's independent check |
| `zkc.structured-source/0` | [Cutover](formats/foundation-interfaces.md#structured-source), IR / Protocol | Structured exporter → independent semantic readers | Native readers validate complete structured types, bindings and parameters, including nominal resource-unit Slot arguments; independent formal resource-unit interpretation is not implemented. The formal reader preserves logical-sort oracle descriptors and logical-record origins. New total-word meanings and oracle execution await formal interpretation |
| `zkc.constructed-participant/0`, `zkc.constructed-pair/0` | [Cutover](formats/foundation-interfaces.md#constructed-participants), IR / Construction | Actual candidate export → independent construction/projection readers | Native participant/pair producers and the formal constructor bridge use closed structured codecs; checked connection certificates establish the admitted formal profile |
| `zkc.oracle-realization/0` | [Cutover](formats/foundation-interfaces.md#realization-and-application-records), IR / Transforms | Realization producer → native actual-body reader, independent interpretation | Native structured type inventory and actual-body reader implemented; independent interpretation unsupported |
| `zkc.application-map/0` | [Application map](formats/application-map.md), IR / Transforms | Source/candidate association → native comparison, independent correspondence reader | Producer and independent actual-candidate checker implemented for unsimplified preparation; written links from a strictly read source correspondence, with `absent`, `conditional` and `checked` status; no correspondence theorem or simplified-rewrite profile implied |
| Checked selected endpoint closure | [Computation](ir/computation.md#selected-endpoint-closure), IR / Compiler | Complete constructed closed Exec → common endpoint reader → CPU physical selection and EVM legality | Both targets retain complete source correspondence separately from the selected executable inventory; each target owns its lowering and executable admission |
| `zkc.evm-source/0`, `zkc.evm-artifact/0` | [EVM target](targets/evm.md), EVM compiler and SDK | Checked verifier → legalized EVM/Yul → pinned solc → authenticated SDK artifact → deployed verifier | One library producer emits the source response, with the source Entry distinct from the policy's entry and without tool facts; its options are the CPU package's shared list. Shared logical layouts, prime/extension arithmetic, finite/structured transport and fork-bound options; deployed differential evidence, with cryptographic expansion and formal lowering correspondence separate. Conditional participant completion in the selected verifier refuses by name with `evm.completion`; its outcome-lane lowering belongs to the EVM compiler and SDK owner |
| `zkc.evm-target/0` | [Target declaration](targets/evm.md#target-declaration), EVM compiler and SDK | `common/targets/evm.json` → compiler generator and tables, Rust SDK build and `zkc::evm_target`, deployed runner and harness | The compiler generator and the Rust SDK build each validate it against the shared refusal cases. The compiler reads only its generated tables, and its `zkc.evm-source/0` response names the declaration identity, which the SDK's response reader requires to equal its own. The SDK and CLI read the generated `zkc::evm_target` module. The deployed runner checks each declared fork against its engine, and the harness checks the declaration with its validator; both read every target fact from it |
| Outcome, stop, budget meaning | [Native foundation](ir/native-foundation.md#outcomes-observations-and-budgets), IR / Execution | Typed invocation → compiler admission and native VM/providers | Typed route implemented; existing reached schedule, stops and budgets retained |
| Restricted record custody and succession | [Source restrictions](language/definitions.md), [distributed records](language/records.md), [translation](language/translation.md), Language / IR | Checked instantiated record layout and consuming home APIs → independent interface readers, actual-body comparator, native resource-origin analysis, native proof admission and unit backend | Explicit linear/affine ordinary and fixed-roster distributed wrappers retain nominal custody, including zero storage. Catalog-associated inspect_record/repack_record preserve exact roots, ordered role maps, placed Copy/Drop payloads, authored lexical authority and child-to-SSA provenance across helpers and existing repeats; actual comparison checks every fragment pass. Consume/create replacements still refuse. Source-selected control integration and independent formal-consumer migration remain separate work |
| Native branch origin frames | [Native occurrences](ir/construction.md#native-occurrence-encoding), IR / Contracts | Typed native origin and byte writer → native readers and independent format/runtime consumers | Four-field branch frames retain declared arm labels. C++ and Rust typed/byte readers implement the shape; source-origin producer integration and independent formal-reader migration remain separate |
| Selected Protocol and Math control | [Selected regions](ir/control.md#selected-protocol-and-mathematical-regions), IR / Protocol and Data | Registered closed arms and derived common-input requirements → native admission, interaction consumers, actual projection/correspondence and exact resource origins | Protocol arms retain native Exec outlining; selected Math uses recursive computation recipes, arm-local scoped conditional/match bodies and independent actual-candidate comparison through normalization and realization. Source emission, common-input export and SDK admission are integrated for the supported profile and paired with fresh compiled packages; Program and Rust selected execution are implemented. Formal interpretation is listed under formal reader status. Oracle analyses retain arm coordinates. Native proof construction, reverse request planning, native codec construction and oracle realization refuse selected Protocol or Math control in the selected entry's [static closure](ir/control.md#analyses-and-construction): its dormant arms, applications, helper and local calls and referenced declarations. A declaration outside that closure, such as an uncalled helper or protocol, does not gate the entry |
| Native successor operands | [Execution branches](ir/execution.md#structural-branch-interfaces-and-admitted-execution), IR / Data and Exec | Native builders and source emitter → BranchOpInterface clients, source readers and correspondence checks | Independent forwarded segments implemented; generic CFG publication still requires semantic binding, custody and budget correspondence beyond structural formation |
| Stage admission and target selection | [Stage pipelines](ir/native-foundation.md#stage-pipelines-and-target-selection), IR / Compiler | Shared stage builder and selected installation → API, textual pipeline, import and publication | Shared stage builders, typed selection and complete native admission; catalog availability does not establish an installed backend |
| `zkc.program/0` | [Retained byte language](formats/foundation-interfaces.md#executable-byte-language), IR / Program | Compiler → independent C++/Rust readers and other target consumers | Participant loop, if and match captures use explicit local/parent bindings; selected participant control has all-arm admission. The native producer and independent C++/Rust readers are implemented and share the program byte controls. Formal interpretation is listed under formal reader status |
| `zkc.input-bindings/0` | [Trusted input bindings](formats/input-bindings.md), Runtime / Host | Externally pinned application context and independently derived or application-trusted exact requirements → Runtime/SDK actual input checks | Pin, subject and typed value/tag/extent checks; SDK requires every Protocol inventory, checks canonical classes and source paths, and resolves the selected original through the existing component map and actual Program. Portable participant checks precede Runner loading; named joint checks precede issuance. Native inventory derivation, comparison and publication are integrated; the explicit fresh-compiler pairing gates bind compiled packages' inventories to actual named runs. No agreement certificate or formal interpretation |

### Current producers and consumers

`Implemented` describes the named producer/consumer profile, not all possible
consumers. `Partial` names a missing consumer or behavior. `Designed` has no
production format or admission authority. The last-PR column records the last
contract change, not the most recent documentation-only registration.

| Identifier / version | Owning specification | Single owner | Producer → consumer code | Status | Stages or links introduced | Last PR |
|---|---|---|---|---|---|---|
| `zkc.compilation-observation/0` source work | [Source work observation](language/definitions.md#bounds-and-scope) | Frontend / Language accounting; compiler driver diagnostic output | Language `Work`, checked/analysis/closure accessors → [source driver](../../compiler/lib/Driver/Language.cpp) → [SDK diagnostic transport](../../crates/zkc/src/project/compiler.rs), CLI reports | Native producer and accessors implemented with source-level regression coverage; execution validation pending. SDK transport accepts diagnostic JSON without a strict field schema. Independent formal readers do not consume this diagnostic surface. Completed ledgers expose every subphase; independent checks and Host children remain explicit | None; diagnostic only, no admission or authority | — |
| `zkc.source-ast/0` | [Written source](language/source-ast.md) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → future Lean elaboration reader | Partial: both native grammars and neutral formal nodes exported; independent source reader remains open | None; does not discharge `source.correspondence` | [#186](https://github.com/zkcompiler/zkc/pull/186) |
| `zkc.source-bindings/0` | [Binding proposals](language/source-ast.md#source-binding-proposals) | Frontend / Language | [WrittenSource.cpp](../../compiler/lib/Language/WrittenSource.cpp) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: retained resolutions; no elaboration soundness theorem | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-instances/0` | [Closed instances](language/source-ast.md#closed-source-instances) | Frontend / Language | [Compiler](../../compiler/lib/Compiler) → [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp), future Lean elaboration reader | Partial: closed instances and mandatory unresolved oracle construction substitutions with whole-Formula lookup keys; independent source/IR occurrence association, expected-type checking and call-edge proof remain open | None | [#180](https://github.com/zkcompiler/zkc/pull/180) |
| `zkc.source-correspondence/0` | [Checked elaboration](language/elaboration.md), [generated definitions and occurrences](language/source-ast.md#generated-definitions-and-occurrences) | Frontend / Language | [SourceCorrespondence.cpp](../../compiler/lib/Compiler/SourceCorrespondence.cpp) → [bridge inventory](../../lean/bridges/pipeline/source_inventory.py) and future Lean correspondence checker | Native producer and exact-artifact bridge checks cover source context, authored/generated rows, substitutions, complete ordered sites and written references; installed declarations have no captured source spans. Semantic source correspondence remains open | Proposed source-to-admitted connection | [#185](https://github.com/zkcompiler/zkc/pull/185) |
| Structured source, version 0 | [Structured source](formats/structured-source.md) | IR / Protocol | [StructuredSource.cpp](../../compiler/lib/Compiler/StructuredSource.cpp) → [Lean structured reader](../../lean/Zkc/Source/Structured) | Partial: strict Lean type/binding/parameter reading, logical-record origins and complete oracle input/component logical sorts are installed; new total-word meanings and oracle execution remain outside the ordinary formal profile | Existing source interpretation; wire recognition grants no oracle execution admission | [#194](https://github.com/zkcompiler/zkc/pull/194) |
| Logical oracle operations and kinds, version 0 | [Protocol oracles](ir/protocols.md#logical-oracle-kinds-and-handles), [wire operations](formats/structured-source.md#logical-oracle-vocabulary) | IR / Protocol | [OracleOps.td](../../compiler/include/zkc/Dialect/Protocol/IR/OracleOps.td), [Protocol formation](../../compiler/lib/Dialect/Protocol/IR/Oracles.cpp) → [realization](../../compiler/lib/Transforms/OracleCommonRealization.cpp), frontend emission, Lean reader | Native table/virtual semantics, checked source projection and realization implemented; the independent Lean reader preserves logical-sort descriptors and sequence capacity; oracle execution still needs independent Lean interpretation | No new registered claim stage | [#194](https://github.com/zkcompiler/zkc/pull/194) |
| `zkc.oracle-obligations/0` | [Oracle proposals](formats/structured-source.md#oracle-obligation-proposals) | IR / Protocol | [OracleObligations.cpp](../../compiler/lib/Compiler/OracleObligations.cpp) → native comparison and Lean independent derivation | Partial: independently checked occurrence-bound templates and footprints; no predicate discharge | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.oracle-realization/0` | [Realization record](formats/oracle-realization.md) | IR / Transforms | [OracleRealizationRecord.cpp](../../compiler/lib/Transforms/OracleRealizationRecord.cpp) → [actual-body reader](../../compiler/lib/Transforms/OracleCommonVerification.cpp), future Lean realization reader | Native checked table and virtual queries, dynamic complete-window authentication and ordered replay implemented; Lean simulation open | Realization is a compiler boundary; `realization.correspondence` remains unregistered | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.oracle-selection/0` and requested compiler policy | [Requested selection](formats/oracle-realization.md#requested-selection) | IR / Compiler | C++ API, CLI and SDK settings → exact source-derived selection admission and packaged options | Implemented uniform/exact requests through C++/CLI/SDK, source-relative admission and mandatory packaged policy | None; selected implementation is not a binding or simulation theorem | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.constructed-participant/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.constructed-pair/0` | [Constructed participants](formats/constructed-participant.md) | IR / Construction | [Compiler](../../compiler/lib/Compiler) → [structured bridge](../../lean/bridges/structured), [Construction](../../lean/Zkc/Construction) | Implemented within admitted profiles | Supplies subjects for `construction.checked`; export alone does not discharge it | [#173](https://github.com/zkcompiler/zkc/pull/173) |
| `zkc.program/0` | [Program bytes](formats/program-bytes.md) | IR / Program | [Encode.cpp](../../compiler/lib/Program/Encode.cpp) → [Decode.cpp](../../compiler/lib/Program/Decode.cpp), [native VM](../../crates/zkc-runtime/src/vm), [Lean renderer](../../lean/bridges/executable/render.py) | Partial: native readers and shared corpus; Lean installed table has a narrower profile | Input to `lowering.interpreted_bytes`; native runtime conformance separate | [#179](https://github.com/zkcompiler/zkc/pull/179) |
| Retired Common source | [Structured-source replacement](../../lean/docs/spec/structured-source.md) | Former IR / Compiler, Lean / Source | No retained producer or reader | Retired in favor of original structured source and its Domain interpretation | No additional admitted link | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.language-interface/0` | [Language interface](formats/entry.md) | Frontend / Language | [LanguageInterfaceWriter.cpp](../../compiler/lib/Compiler/LanguageInterfaceWriter.cpp) → [native comparison](../../compiler/lib/Compiler/LanguageInterfaceComparison.cpp), [Rust Host](../../crates/zkc/src/entry/interface/raw.rs), [Lean bridges](../../lean/bridges) | Recursive strict schema includes required per-Protocol common-input inventories. SDK validates every local inventory, canonical classes and typed source paths, reuses placement/component maps, and binds the selected original to actual Program types. Closure derives and retains every closed concrete Protocol inventory under its source allowance. Publication/comparison borrows it and charges current layout, component mapping and normalization work across Protocols; independent native reading derives obligations from the actual original and checks exact canonical classes. One source-to-native mapping, over the published component map, serves the independent native comparison. Fresh source-to-SDK pairing covers named CPU admission and retained Host families. Independent formal interpretation remains a separate gate. Existing custody, generated identity, privacy, formula and constructor rules remain; logical handles stay outside Host byte payloads. Schema `identity` is the [revision-bound nominal identity](language/definitions.md#nominal-authority); the C++ reader recomputes retained nominals over the carrier's authority rows, and the Rust SDK compares published identities without computing a revision | None | [#177](https://github.com/zkcompiler/zkc/pull/177) |
| `zkc.host/0` | [Entry Host](formats/entry.md) | IR / Translation | [Direct native emitter](../../compiler/lib/Translation/Entry/Emission.cpp) → [independent SSA artifact reader](../../compiler/lib/Translation/Entry/Reader.cpp), [Rust Host](../../crates/zkc/src/entry) | Implemented: actual Func/CF ports, layouts and outcomes determine the artifact; no retained body or signature JSON. Native generated signatures and Rust child admission transport exact typed whole ordinary values; split ancestors and external setup data retain constructor checks | Native source comparison only | [#187](https://github.com/zkcompiler/zkc/pull/187) |
| `zkc.run/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Selected Program/schedule admission and execution implemented; native selected producer/fixture integration remains open. Existing unconditional publication profiles remain separate from selected proof/oracle refusals | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.entry/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers and checked oracle proof publication; logical claim transport and formal realization remain open | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.native-proof/0` | [Entry](formats/entry.md), [proof](formats/proof.md), [joint execution](runtime/joint.md) | IR / Compiler | [Compiler](../../compiler/lib/Compiler) → [Entry Host](../../crates/zkc/src/entry), [proof Host](../../crates/zkc/src/proof), [joint Host](../../crates/zkc/src/run) | Implemented native carriers and checked oracle proof publication; logical claim transport and formal realization remain open | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| Deterministic verifier-request construction, version 0 | [Request relation and target schema](ir/verifier-requests.md) | IR / Compiler | Checked realization → participant construction and independent actual-body reader → native descriptor and executable endpoint admission | Implemented checked reconstruction, reconstructed-message events, normalized selection and independent native endpoint admission; ordinary oracle/FRI proofs execute; no runtime SSA certificate carrier | No new assurance stage | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| `zkc.contract-declarations/0` | [Shared catalog](formats/contract-declarations.md) | IR / Contracts | [Neutral source](../../common/catalog/README.md) → C++/ODS, [Rust metadata](../../crates/zkc-catalog/README.md) and serialized inventory; [Rust admission](../../crates/zkc-runtime/src/vm/operations/mod.rs) interprets declarations with independently owned backend installations | Partial: native and Rust projections consumed; the formal bridge decodes structural metadata and independently derives installed primitive signatures; new native operations require separately installed Lean meanings. Installed-instance tables and the `Succession` facet are validated by all three generators and generated into C++ and Rust tables; the C++ and Rust owners and consumers read them, while the formal readers keep their own tables | None; signatures do not prove kernel laws | [#187](https://github.com/zkcompiler/zkc/pull/187) |
| `zkc.native-installation/0` | [Native installation](formats/native-installation.md) | Runtime / native installation | [Installation source](../../common/catalog/README.md), packaged and checked with the declarations → C++ Contracts and CPU target, `zkc-runtime`, zkc-cpu | Partial: validated by all three generators and generated into C++ and Rust tables; C++ Contracts, the CPU target, `zkc-runtime` and zkc-cpu read it, and actual target support remains each target's independent check | None; physical choices grant no meaning or support | None |
| `zkc.source-claims/0` | [Source requests](language/claims.md) | Frontend / Language | [Language SourceClaims.cpp](../../compiler/lib/Language/SourceClaims.cpp), [compiler export](../../compiler/lib/Compiler/SourceClaims.cpp) → [Lean bridges](../../lean/bridges) | Implemented original-grammar requests; new frontend integration pending | Selects an existing stage; introduces none | [#176](https://github.com/zkcompiler/zkc/pull/176) |
| `zkc.bound-source-claims/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.subject-evidence/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.declarations/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#182](https://github.com/zkcompiler/zkc/pull/182) |
| `zkc.assurance-report/0` | [Assurance pipeline](../../lean/docs/spec/assurance-report.md) | Lean / Claims | [subject bridge](../../lean/bridges/subject.py), [Claims](../../lean/Zkc/Claims) → [record checks](../../lean/checks/check_records.py) and report consumers | Implemented within registered subject profiles | Registered stages and links below | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.consumer-requirements/0` | [Independent consumer scope](../../lean/docs/spec/assurance-report.md) | Lean / Claims, with frontend consumer integration | Independent consumer file → [record checks](../../lean/checks/check_records.py), Lean receipt audit → report consumer | Partial: independent occurrence/context input and post-audit coverage; frontend producer integration pending | Adds omission accounting; changes no receipt meaning or stage | [#188](https://github.com/zkcompiler/zkc/pull/188) |
| `zkc.companion/0` lookup identity and obligation inventory | [Companions](language/companions.md) | Frontend / Language | Authored inventory and generated lookup addresses → [Lean typed resolver](../../lean/ZkcTools/Companions.lean) and [assembly](../../lean/ZkcTools/Companions/Assembly.lean) | Partial: lookup keys, mandatory pending postconditions and native whole-Formula oracle-admissibility addresses implemented. Oracle occurrence substitutions remain unresolved; independent source/IR association, oracle expected-type checking and proof discharge remain open. Existing Lean typed resolution/assembly and retained Entry-origin/closed-instance lookup are installed within their profile; intermediate source spans remain open | None; existing Lean admission remains authority | [#185](https://github.com/zkcompiler/zkc/pull/185) |
| Layout requests and authored site selection | [Layout syntax](language/layout-syntax.md), [site defaults](language/layout-execution.md) | Frontend / Language | Lossless syntax and native projection → written occurrences and pending obligations | Partial: source association retained; typed request generation and independent checking pending | Selects existing meanings; adds no assurance stage | [#186](https://github.com/zkcompiler/zkc/pull/186) |
| Canonical home-method invocation | [Method binding](language/definitions.md#arguments-and-inference) | Frontend / Language | Declaration index and receiver inference → ordinary call binding, immutable invocation/value reconstruction, native emission and actual-body comparison | Nominal and generic-alias homes; complete receiver-derived role maps for existing direct logical families. Managed methods use the same index with nominal constructor ownership and exact authored-query witnesses; replacement record placements remain open. Existing written-source formats are unchanged; independent formal elaboration remains separate | No new assurance stage | — |
| Retired proposal `zkc.lean-interface/0` | [Shared interfaces plan](../roadmap.md#shared-interfaces-before-implementation) | Frontend / Language | Existing declarations and bound requests → frontend resolution | Retired proposal: extend existing transports; no parallel format is admitted | None | — |
| Recursive record placement and custody | [Record placement](language/record-placement.md), [Entry carrier](formats/entry.md), [SDK admission](runtime/entries.md) | Frontend / checked model; native lowering and interface consumers | Checked product schemas and role applications → native component observation, independent candidate reader, SDK component admission, Lean-owned reader | Placement core and Rust ordinary component supply implemented: exact role-intersection visibility, indexed work-bounded public selections, semantic empty coverage, indivisible setup variants, participant native ordering, operation-scoped external ingress and typed whole-value transport. Source closure publishes schemas and component maps without judging external supply; the SDK's shared Entry admission is the only owner of that judgment, per [operation and supply mode](runtime/entries.md#external-supply), while source, construction, setup, schema/native, backend, carrier-reader and EVM calldata checks keep their owners. SDK output collection and generated bindings retain opaque storage with checked public projection; whole-value reimport checks exact schemas, while inaccessible JSON and physical-backend output paths refuse explicitly. Constructor, privacy, sealing and custody remain independent. During brace-profile migration, the exact current schema also admits telescope-free Copy/Drop logical records with one checked oriented family; required fields never default. Remove that alternative with the Layout seam and brace parser at cutover. Native current-schema publication is implemented, and the explicit fresh-compiler pairing gates execute compiled component families. Formal readers are listed under formal reader status | No new claim stage or receipt status | — |
| Native index blocks and gated requests, version 0 | [Request bytes](formats/native-index-block.md), [construction](ir/construction.md#native-index-blocks) | IR / Construction | Native construction → independent actual-body and Rust readers, CPU bounded search/check, SDK transport | Native compiler/runtime integration; independent Lean adaptation remains open | No registered gate premise or Fiat–Shamir theorem | — |
| `zkc.construction-binding/0` | [Closed binding profiles](ir/construction-binding.md) | IR / Compiler | Actual original/candidate correspondence → canonical encoding/state analysis → complete recomputation | Native history, canonical hash history and explicit-input coverage; bounded closed profiles | Primitive interpretation, host initialization and cryptographic premises remain explicit; not a security theorem | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Source-selected gates, version 0 | [Proof choices](language/entries.md#proof-declarations), [written syntax](language/source-ast.md) | Frontend / IR | Checked labelled query paths → source/interface comparison, native selection and SDK artifact binding | Required `gates` proof-job field and written `gate` nodes; native policy and witness wire unchanged | Direct installed block construction only; no security theorem from difficulty | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Expanded local occurrence names | [Function origins](ir/functions.md#origins-and-identity), IR / Algorithms | Scoped expansion and numerical realization → independent correspondence readers and emitted native sites | Full length-delimited paths remain in origin records; long names use the complete SHA-256 digest in unpadded base64url; native producers and checkers change together | Names do not establish correspondence; independent formal consumers are not migrated here | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| CPU retained-value profile | [Native capacity](runtime/capacity.md#retained-values-and-logical-work), Runtime / CPU | CPU value constructors, preflight and codecs → VM retention and shared execution ledgers | 80-byte inline slots; large group points, complete variant nodes and aggregate metadata use charged immutable backing; expanded value bounds and live capability validation remain independent | Native resource accounting only; no new formal claim | [#193](https://github.com/zkcompiler/zkc/pull/193) |
| Parameterized STARK degree reduction | [Assignment inventory and DEEP contract](domains/stark.md) | Libraries / IR | Captured Bundle → extended OOD inventory → adjusted first FRI word and authenticated query association | Implemented native profile; degree-boundary adversary, full-column inventory and scalar/product/gated quartic Keccak deployments exercised | No complete DEEP/FRI, commitment or FS theorem for this compiled client | [#196](https://github.com/zkcompiler/zkc/pull/196) |
| Installed transcript and Merkle suites | [Transcripts](ir/construction.md), [Merkle schemes](domains/oracles.md), [services](runtime/services.md) | Runtime / Providers | [Backend registry](../../crates/zkc-cpu/src/backend/registry.rs) → Contracts selection, native invocation, Lean installed vocabulary | Native quartic Keccak rows, randomness and hash-chain transcript installed; independent Lean coverage remains separate | Kernel interpretation remains explicit | [#174](https://github.com/zkcompiler/zkc/pull/174) |
| Mathematical participant projection bound | [Compiler limits](ir/limits.md) | IR / Mathematical | [Mathematical.cpp](../../compiler/lib/Transforms/Mathematical.cpp) → `mathematical-projection-limit` before participant bodies are built | Implemented at 100,000 role-node visits per common body. Measured profile: a trivial 1,024-role Protocol with one port has 10 nodes (10,240 visits); one port per role gives roles + 9 nodes, so 311 roles (99,520 visits) is the largest such roster and 1,024 roles need 1,057,792. A 1,024-role Protocol admits at most 97 nodes. IR owns calibration against the `protocol.roles` roster | Role-node visits | — |
| Common-input inventory bound | [Entry carrier](formats/entry.md) | Frontend / Language | [CommonInterface.cpp](../../compiler/lib/Compiler/CommonInterface.cpp) → `source.limit` "common inventory limit exceeded" in source publication, source comparison and the C++ reader; the SDK reader refuses with `entry-interface-limit` | Implemented at 1,024 classes, 32,768 components and 32 path steps per Protocol, within the enclosing `Limits::work` allowance. Measured profile: one input and one output per role derive no class, so a 1,024-role Protocol publishes an empty inventory; a Boolean input at every role observed by a branch is one class with one component per role. Mathematical admission's separate 1,000,000-unit common-control allowance refuses first: with one such input from 407 roles, and at two roles from 210 inputs, while 1,025 inputs at two roles refuse at source publication with the inventory limit. The frontend owns calibration | Classes, components, path steps, work units | — |
| Structured-source publication ceiling | [Structured source limits](formats/structured-source.md#limits-and-evidence) | IR / Protocol | [StructuredSource.cpp](../../compiler/lib/Compiler/StructuredSource.cpp) → `structured-source-limit` "publication exceeds 1 MiB" in the structured export and in every native analysis that reads the exporter's source view: application-map production and checking, oracle obligations, source correspondence and source claims | Partial: the export accepts the full `protocol.roles` roster and bounds the published file at 1 MiB. The native analyses above obtain their view from the exporter, so a subject whose publication alone exceeds 1 MiB refuses there with the same diagnostic. Measured profile: each port scope that lists all 1,024 native role names adds 15,382 bytes; a 1,024-role Protocol with one Boolean input per such scope publishes 67 of them in 1,046,261 bytes and refuses at 68. The IR session's native source admission and publication package receives the separation of native admission from this publication ceiling | Output bytes | — |
| Installed source declarations and notations | [Installed declarations](formats/contract-declarations.md#installed-source-declarations), [installed modules](language/definitions.md) | IR / Contracts (rows), Frontend / Language (reader) | `frontendDeclarations`, `frontendNotations` and `frontendConstructors` → generator, zkc-tblgen and Rust validators, which check home constructors against the type and frontend-constructor rows rather than a list of names and require one frontend-constructor row per form; [InstalledDeclarations.cpp](../../compiler/lib/Language/InstalledDeclarations.cpp) → declaration index, and [Builtins.cpp](../../compiler/lib/Language/Builtins.cpp) → logical heads formed only from the frontend-constructor rows | Implemented: `zkc::prelude` and `zkc::records` are read from the rows, with no embedded or written source; rule associations are bodiless `installed` definitions, primitive associations keep the primitive path, and installation identity frames every row. Explicit prelude membership supplies the index fallback; catalog service methods enter the index as installed declarations with stable method identities and nominal constructor ownership | Catalog source associations | — |

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
| `zkc.native-origin-template/0`, `zkc.native-origin/0` | IR / Construction | [Logical event path and actual repeat coordinates](ir/construction.md), with explicit branch alternative frames; native-origin bytes enter the transcript and cannot be changed for display convenience |
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
| Nominal identity | Canonical key: the lookup key plus each named declaration's source authority | Custody slots, nominal descriptors and schema digests carry it; the interface reader recomputes it over the retained authority rows; only the frontend comparison checks revisions against source bytes. Lookup keys and symbols bind no revision. |
| Structured row | Exact snapshot/admission plus row | Actual-module reader checks ports, operations, ordering and origin associations. |
| Emitted site | `(definition, site)` in the exact snapshot | Emission records each site's originating expression and each generated definition's origins; the correspondence occurrence row joins the site to its written nodes under the completeness invariant. |
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

Every source-package manifest and every explicit SDK or CLI module map selects
its [source format](language/definitions.md); the SDK forwards that one selection
to the compiler and frames it into its cache key, without a default. The runtime
owns the cutover that retires the `zkc` value. Frontend syntax support does not
retire it; the source/request connection and host/editor consumers satisfy their
owning contracts first.

The scalar-selection addition keeps the current `/0` declaration and program
formats: four exact operation rows (`bool.select`, `index.select`,
`field.select<F>`, `curve.select<G>`) implement the existing mathematical
`arith.select` profile. Catalog projections, native installation, independent
recipe readback and CPU advertisement change together. See [value meanings](domains/values.md#total-scalar-selection)
and [mathematical realization](ir/mathematics.md#scalar-selection-realization).
Independent formal consumer admission is not enlarged by these native rows.


## Selected source admission handoff

The [selected source control contract](language/selected-control.md) owns the
Language producer's exact immutable input/path/role obligations and their
original-native/participant-ABI mapping. Translation independently compares all
actual native arms, including dormant bodies, service aliases and yields.
Source recurrence independently checks demanded initial and yielded observations
under grounded induction for exact loop invocations. The concrete-Protocol
handoff also supports retained helper inventories. Paired original validation
compares complete canonical equality classes by exact type and observation
after source layout flattening; neither derivation is the other's authority.
[Structured source](formats/structured-source.md#selected-source-regions) and
application maps retain arm coordinates and ordered role substitutions. These
inventories are admission requirements, never common-value certificates.
The Entry/SDK owner must consume the exact mapped components through actual
joint reached checks or externally pinned independent input binding. Native
common-control analysis, executable admission, selected oracle/security
profiles and independent formal consumers retain their separate integration
and evidence boundaries.
