# Implementation review

This review asks whether an accepted security claim is about the actual imported
program and authored relation, whether its experiment is explicit, and whether
the architecture supports reuse without copying proofs for each source form.
The implementation passes were followed by independent read-only agent reviews
of the semantics, source bridge, security proofs, architecture, external FS
theorem applications and certificate automation. These are agent reviews,
not a human external audit. The [support matrix](../support.md) owns the supported claims.

## Architecture and composition

The core imports Mathlib and has no ArkLib, VCVio or Clean dependency. Security
adapters and the Clean relation exporter have separate Lake packages and exact
shared dependency pins. Module-header and declaration-body audits enforce the
direction from generic semantics to protocol contracts to source clients.
Particular source examples do not enter generic security consumers.

`Certificate.verify`, contract adapters and property consumers provide typed
extension points. The custom rejection consumer demonstrates a downstream
property for an imported Schnorr program without a compiler or registry change.
Sumcheck residual contracts and the factor-opening example test sequential
composition with shared state, adaptive replies and a bad-opening event in one
joint experiment. Their error bound adds the opening loss; no independence is
inferred from separate service names.

## Semantics and source boundary

The review distinguishes a returned false decision, rejection, handler stops,
missing replies and an unfinished observation prefix. Well-founded open processes
embed into the machine model, with resumption and completion laws. Runtime by-value bounded loops now have a structured import; general native
branches, Local control and external waiting remain outside the exported profile.

Native differential execution reads SSA independently of the exporter and
compares full selected observations with the Lean executable over Z/97. Generated
programs exercise arithmetic, role restrictions, communication, service queries,
guards and helper expansion. Malformed inputs and a deliberately changed
arithmetic operation test rejection and discrepancy detection. These are finite
adequacy checks, not a proof of production arithmetic or compiler correctness.

## External proof chains

The ArkLib adapter proves the polynomial-message representation, statement and
domain laws, statement-oracle realization, reached-query execution equality and
accepted-event equality before applying ArkLib's native interactive Sumcheck
soundness theorem. The public two-round degree-two interface admits causal
coefficient-message strategies and arbitrary private probabilistic mixtures
chosen before fresh verifier draws.

The VCVio adapter proves a bijective uniform-sampling transport for Schnorr's
honest transcript and witness-free simulator, including the actual imported
verifier's outcome. This is a fixed honest-challenge, one-session simulation
claim. Neither adapter establishes Fiat–Shamir or malicious-verifier security.
The factor-opening example has a proved public-polynomial instance and a
conditional opening-error bound; it does not supply a PCS security theorem.

## Author intent and proof construction

The named specification selects the contract, property, experiment, roles,
inputs, effect sites and authored target. The interface resolver checks the
source identity and actual selectors, then exports the relation's formula body.
A matching name alone cannot establish the relation. Lean connects the admitted
formula and actual verifier through a generated target special-soundness theorem.

Candidate construction and requested-subject checking reconstruct the source
separately. Controls reject a valid certificate for a different program, copied
positive identities, false relation bodies with expected names, wrong relation
certificates, stale selectors and unsupported experiments. Transitive axiom
checks reject proof holes; the audit controls also test unused axioms, native
evaluation axioms and empty module selections. The resolver and renderer remain
reviewed/tested trusted software boundaries, stated explicitly in receipts.
Generators now return restricted pure expressions, not Lean command streams.
The renderer owns declarations and audits, and the checker retains independent
input snapshots. Python execution and the selected toolchain remain trusted.

## Findings resolved during implementation

| Finding | Resolution |
|---|---|
| Latest VCVio removes modules still imported by ArkLib | Pin and test a coherent dependency closure; record the concrete incompatibility |
| A generic `Examples` Lake library collides with upstream examples | Use `ZkcExamples` and test standalone downstream imports |
| Prior source syntax and identities were stale | Re-export from current DSL and recheck exact correspondence |
| A valid protocol proof can hide a wrong authored relation | Check the actual formula body and reconstruct the requested relation subject |
| Constructor rendering could ignore surplus instruction fields | Check exact array arities and source identities before generation; add malformed-export controls |
| Upstream builds contain unrelated proof holes | Audit the transitive dependencies of every claimed owned result |
| Clean's unrelated VM development fails on the new Mathlib | Keep the isolated flat-AIR adapter; prove channel refusal for arbitrary channel operations |
| Deleted models left stale native documentation claims | Remove obsolete proof claims while retaining native mathematical obligations |
| Core checks could resolve optional dependencies | Select core-only boundaries in the default runner; check integrations explicitly |
| A negative test could accept signal termination as refusal | Require an ordinary positive error exit |
| A candidate command stream could terminate before subject checks | Admit only restricted pure expression proposals; let reviewed rendering own all Lean commands and audits |
| A generator could mutate the source or requested properties shared with the checker | Pass disposable copies and retain independent checker/receipt snapshots; test source and request changes |
| Native and Lean replay parsers disagreed on signed zero and unused malformed replies | Require unsigned integer tokens and tagged arrays throughout requests; compare both executable refusals |
| The native Lean check could use a missing or stale core executable | Build the main Lean package before native differential checks |
| Maintenance instructions and bridge links retained obsolete versions/paths | Align the guide with the manifests and include bridge Markdown in link checks |
| New parser refusal controls could count a crash as rejection | Require exit 1 and each reader's exact diagnostic; separately exercise non-refusal exit codes |
| A repeated successful request inflated the reported source count | Name the metric `verified_requests`; test nested source, request and relation mutations |
| New foundation modules were absent from aggregate audits | Regenerate exhaustive core/security import roots, including constructed replay |
| An FS command-line parse failure could preserve a stale success receipt | Acquire output ownership and invalidate prior success before complete argument parsing; exercise the public CLI |
| Concurrent output reuse could detach a receipt from the certificate Lean checked | Lock each output directory, use a private invocation-specific proof file, and recheck retained subject/proof bytes before publishing success |
| Module-system replay through `lean --run` lacked native implementations | Build and invoke the maintained `constructed-source` executable; resolve CLI paths before changing directories |

## Constructed-program and Fiat–Shamir review

The construction extension received separate read-only reviews of semantic
foundations, security mathematics, and the request/export/certificate boundary.
The foundation and mathematics reviews found no defect in the inspected laws.
The foundation review identified missing aggregate import coverage; maintained
audit roots now enumerate the new modules as well as the constructed replay tool.
These reviews are bounded by the checked source versions and supported profiles.

The actual source-checked candidate is exported independently of the common
interactive source. Its admission retains all primitive replies, guards, Local
handler bodies and final state. Generated normalization exposes a typed program
and proves its exact erasure against the imported syntax, avoiding repeated
evaluation of the entire decoder during dependent denotation proofs. This is a
proof scalability choice, not a relaxation of admission.

Schnorr connects full constructed execution to VCVio's shared cached-oracle
extraction experiment. Sumcheck proves the all-prefix residual knowledge and
existential bad-event bounds required by ArkLib. A fixed salted-key simulation
handles arbitrary full-prefix queries, including inconsistent earlier challenges.
The bound charges its additional query. Early-stop coupling preserves acceptance;
it deliberately does not claim equality of final caches or costs after rejection.

The full denotation equations cover Helpers/Reordered Schnorr and Helpers/Horner
Sumcheck. Source variants share fixed primitive interpretations and consumers.
Mutations challenge missing observations, stale successor state, altered
arithmetic, wrong residuals and foreign bindings. The receipt checker separately
reconstructs the intended actual subject and security theorem type, rather than
accepting a generator-selected alias as the expected program.

The reviews distinguish public binding supplied by the mathematical input from
native Host initialization, and a typed ideal transcript from concrete Merlin.
They also distinguish the theorem's mathematical relation from an authored DSL
target: the FS request does not invoke the separate named-target resolver.
These are explicit connection boundaries, not consequences of successful
normalization. Schnorr's query budget covers prover calls before the added final
verification query; Sumcheck's actual `Q+2` calls and reduction's `Q+3` bound
remain different quantities.

## Reproduction and further research

The [package guide](../../README.md) gives source-only reproduction and maintained
commands. `just test-lean-native` runs differential execution, the source/property
matrix, authored-target controls, constructed execution/codec comparisons,
actual-body normalization and FS security requests; `just test-lean` runs core boundary and audit
controls plus a standalone consumer. Optional security and Clean commands retain
their own clients and fixture checks. Reports record their inputs and outcomes.

The next research extensions are broader source admission, observation-based
refinement, reusable relation adapters, richer adversary interfaces and explicit
PCS compositions and broader Fiat–Shamir constructions. They require new definitions and proofs; current
success receipts do not stand in for them.

## Compositional extension review

The subsequent extension was reviewed through implementation self-review,
independent executable comparisons, kernel checks and exhaustive dependency
audits. No additional independent-agent or human review is claimed for this
extension. The following boundaries were inspected separately:

| Boundary | Resolution and remaining scope |
|---|---|
| Vacuous refinement relations | Execution simulation requires coverage for each declared implementation input and compatible residual observations; probability coupling is separate |
| Translation asserted by syntax erasure alone | Independent raw and flat interpreters have all-input, all-meaning correspondence laws with typed denotation |
| Fixed two-round FS architecture | A heterogeneous finite-round full-prefix experiment reuses ArkLib knowledge laws and VCVio bad-query accounting; Sumcheck instantiates any finite number of variables |
| Completed-path security versus early rejection | The generic security observation does not claim equality of post-rejection caches or costs; the existing early-stop CLI keeps its own consumer |
| Nominal PCS oracle with assumed binding | Actual ArkLib KZG verification, an explicit setup/adversary game and a concrete t-SDH reduction instantiate the evaluation-sum composition |
| Unrestricted upstream hardness premise | State a bound for the actual reduced adversary; no efficient-adversary or asymptotic cost theorem is inferred |
| Runtime loop unrolling or hidden captures | Retain one typed body, actual count/index, carried values and captures; statically check all bodies and compare nested/sequential native executions |
| Rendered Lean subject detached from JSON | Retain a separate JSON tree and prove its structural decoding equation; altered Snapshot constructors fail kernel checking |
| Expensive mismatch checking was counted as a negative result | Compare retained snapshots explicitly before transporting admission, restrict unfolding at subject checks, stop on structured Lean errors, and require ordinary proof diagnostics in mutation controls |
| Kernel reduction of large byte arrays exhausted resources | Move text-capacity checks to the explicit executable preflight and prove structural codecs compositionally; retain executable over-limit refusals |
| Protocol-specific automation copied into each request | Share process/algebra proof search and connect certified normalization to typed certificates; intent and experiments remain explicit |

Native C++ extraction and Local expansion are still tested boundaries. Primitive
mathematics, record bytes, concrete Merlin behavior, Host initialization and
subsequent backend execution require additional connections. The KZG example is
a registered-polynomial evaluation-sum protocol; it is not a complete native KZG
implementation or a multivariate Sumcheck/PCS verifier. The structured native
carrier currently has admission/execution support, not a general FS CLI consumer.
