# K2 Protocol and Fiat--Shamir Validation

> **Document kind:** Temporary validation and falsification record
> **Document state:** Bounded K2 candidate complete; final repository gates
> recorded below
> **Provisional owner:** `pir`, coordinated by `project`
> **Authority:** None. This page records evidence for the non-normative target;
> current authority remains under [`docs/`](../../../../docs/README.md).
> **Disposition:** Retain with the K2 research package until its rationale and
> deferrals have durable homes; do not make a durable page depend on it.

## 1. Exact claim under test

K2 asks whether one finite, language-independent `InteractiveCore` can be
formed, admitted, executed causally, replayed exactly, and interpreted both
with fresh public coins and with one exact Fiat--Shamir construction. The
candidate must make Statement binding, prover and Oracle influence,
public-coin eligibility, challenge namespaces, sampling transitions, reduction
round ordering, and typed failure independently implementable rather than
leaving them as prose predicates.

The durable candidate is split between:

- [`interactive-core.md`](../../../pir/interactive-core.md), which owns Core
  formation, scopes, bindings, effects, native finite Oracles, claims,
  reductions, causal execution, replay, and public-coin eligibility; and
- [`fiat-shamir.md`](../../../pir/fiat-shamir.md), which owns transcript
  construction, exact framing and prefixes, required influence, namespaces,
  sampling, failure, and the same-Core Fresh/FS relation.

The executable instrument is
[`evaluation/k2-protocol-fiat-shamir/`](../../../../evaluation/k2-protocol-fiat-shamir/).
It imports K1's canonical-value and typed-ID implementation. It is a bounded
semantic pressure instrument, not a second complete K1 evaluator, compiler
implementation, or cryptographic proof.

## 2. Selected contract

The selected K2 model has these load-bearing properties:

1. one literal Core fixes verifier-observable interaction; Fresh and FS are
   distinct challenge interpretations and therefore distinct Protocols;
2. prover moves are generated one decision at a time from a prefix-only view;
   whole-record replay is a separate, weaker relation;
3. every public input is bound as Statement, SessionContext, or
   PublicParameter in an explicit scope before that scope's dependent
   challenge;
4. transcript actions and required influence are derived from Core and exact
   supported module meaning, never selected by an authored absorb flag;
5. public-coin eligibility is a finite dependency computation with no authored
   recomputability Boolean;
6. logical immutable Oracle publication/query/answer is first-class, while
   Merkle/BCS commitment and opening remains a separate construction;
7. reduction publications record their mechanically checked least following
   required challenge, preserving final responses while rejecting
   Last-Challenge reorderings;
8. challenge namespaces use exact semantic occurrence coordinates and draw
   ordinals rather than human domain strings;
9. squeeze bytes, state advancement, acceptance, and decoding are separate
   one-result K1 algorithms; every retry advances state; and
10. sampling exhaustion is one exact module-owned K1 semantic failure, while
    provider disagreement, unsupported evaluation, and resource exhaustion
    remain distinct noncompletion classes.

## 3. Final cold-audit disposition

The single bounded cold audit initially failed seven closure points. K2 did
not discard the factorization; it repaired the missing definitions and laws.

| Cold-audit finding | Disposition |
|---|---|
| raw module declaration references in two canonical bodies | closed by the exact Foundation `Module(...)` union injection at every affected body |
| unformable sampling failure | closed by an exact `SemanticFailureType`, declaration-local payload type, lift equality, canonical coordinate, and payload datum |
| undefined influence and contradictory condition order | closed by the fourteen-case `InfluenceAtom` algebra, exact receipt projection, ordered derived prefix, and condition absorption before comparison and draw |
| asserted public-coin predicate | closed by exact `PCNode`, graph-edge, transfer, sink, and canonical topological-order laws; the authored Boolean was removed |
| incomplete Oracle value/replay model | closed by exact finite carrier, sorted-unique admission, total lookup result, derived output types, scope/lifetime laws, and full/public-binding replay paths |
| underspecified reduction Last-Challenge/sharing law | closed by exact publication kinds, side-input dependency closure, least-following-challenge relation, consumer sequence, and exclusive/shared use law |
| unchecked squeeze-length postcondition | closed by an owner runtime postcondition before state advancement and a distinct fail-closed result classification |

The audit's nonblocking requests were also absorbed: `used_modules` is exact
equality with the derived direct-owner set; simultaneous scope openings have a
fixed depth/ordinal order; and causal-generation provenance is a
nonserializable process-local capability rather than a `RunRecord` field.

A later independent focused review reopened K2 without rejecting its
factorization. The repair and frozen follow-up disposition is:

| Narrow-reopen finding | Final disposition |
|---|---|
| `GuardOutcome` used a generic variant instead of the K1 Boolean carrier | closed by exact `MF`/`MT` frame bodies and K1-backed positive and negative vectors |
| Oracle answers were framed at the bare element type | closed by the exact absent/present lookup-result sum at `OracleAnswerOutputType` and cross-type rejection vectors |
| transcript byte and evaluator authority boundaries were incomplete | closed by typed raw-octet admission, the exact `2^20 - 26` success-payload ceiling, complete tagged-completion preflight, and one retained evaluator identity from Core admission through generation and replay |
| required influence could be read as a second runtime acceptance law indexed by state | closed by exact full-prefix equality as the sole runtime law and a receipt-prefix-indexed ordered-subtrace audit corollary |
| verifier-private Oracle activity was rejected by an incomplete enumeration | closed by the exact descendant-to-`PCSinks(core)` criterion, which admits semantically dead private activity and rejects every live private path |
| terminal and interpretation-failure replay were not one closed input sum | closed by `CompletedProtocolRecord`, exact FS failure recomputation, Fresh/FS variant separation, and explicit nonclaims for partial records |
| the finite instrument overclaimed target conformance | closed by limiting target-exact claims to the two K1-backed frame families and naming the fixture-only lifecycle, evaluator, Oracle, dependency-graph, reduction, and Schnorr boundaries |

One focused follow-up found no architectural blocker, but a separate exactness
audit then found that the first byte calculation had omitted K1's 17-octet
tagged-success envelope and that evaluator and receipt-prefix authority needed
to be explicit. Those points were corrected before closure. A final frozen,
read-only review rechecked the original blockers, the stricter corrections,
and their dependency cone and reported no blocker. This sequence is recorded
because the first positive follow-up was not treated as stronger evidence than
the later counterexample. None of these reviews was a broad cryptographic-
security audit.

## 4. Executable falsifier matrix

The strict runner executes 57 tests. The table records only what those finite
tests observe.

| Obligation | Positive control | Falsifier or contrast | State |
|---|---|---|---|
| exact canonical frame bodies | K1 admits `MF`/`MT` guards and both lookup-result Oracle-answer cases at their exact target types | wrapped Booleans, bare elements, and cross-case/cross-type substitutions fail; canonical bytes distinguish absent from present | passed |
| same-Core Fresh/FS | Schnorr accepts under both interpretations with equal `CoreId` | construction identity changes with Core; Fresh carries no FS state | passed |
| online strategy API and Fresh issuance | honest prefix-only strategy completes; the Fresh resolver is first invoked at its challenge; replay consumes the recorded historical value | future read and strategy stop are noncompletion; invocation carries no future coin; changing resolver output preserves invocation identity; replay alone gains no causal provenance | passed at the bounded Python API; not a host-isolation theorem |
| Statement/scope binding | root and child bindings occur in exact continuous-state order | omitted, late, substituted, unopened-scope, and missing-frame cases fail | passed |
| exact transcript prefix | canonical initialization, guard, message, condition, and draw sequence | omission, duplication, reordering, Wire-only mutation, and altered prefix state fail | passed |
| reduction influence | Schnorr commitment is required before challenge; final response is legal after it | late prerequisite and incomplete side-input publication closure fail | passed |
| public-coin dependency | public dependencies and unused private input remain eligible | direct and transitive verifier-private influence fail FS while Fresh remains available | passed |
| challenge namespace | two draws receive distinct derived occurrence/draw coordinates | duplicate or mutated namespace receipt fails | passed |
| sampling transition | deterministic draw, retry, and typed exhaustion retain advanced state | oversized domain and wrong squeeze length fail at named boundaries | passed |
| native finite Oracle | publication, public query, answer, later challenge, and replay agree | missing extension, lifetime/order, answer, index type, unopened scope, and unknown extension fail | passed |
| claims/terminal/grinding | linear claim closure and explicit grinding message/check complete | duplicate claim use, missing terminal closure, and semantic-sampler conflation fail | passed |

The instrument uses finite Python fixtures, exact enums, and fixture predicates
in places where the durable target uses authenticated K1 declarations and
portable algorithms. Passing it demonstrates inhabitance and first-boundary
behavior for this surface only.

## 5. Frozen exit gate

| # | Result | Basis and boundary |
|---:|---|---|
| 1 | passed | the two routed durable owners now close formation, identity, authentication, admission, execution, replay, Fresh, FS, and their checked relation using K1 mechanisms |
| 2 | passed | strategy-generated execution is prefix-only and replay is explicitly noncausal evidence |
| 3 | passed at K2 scope | every declared public input and scoped binding is structurally complete; completeness against an external Relations Statement remains the named K3 obligation |
| 4 | passed | full prefix equality is the sole independent runtime law; admission-time resolution and the receipt-prefix-indexed ordered-subtrace audit view cover message, Oracle, condition, guard, draw, reduction, and supported-module atoms |
| 5 | passed | occurrence/draw namespaces are derived; the finite dependency graph rejects verifier-private paths to FS-relevant sinks |
| 6 | passed | four one-result algorithms, typed raw octets, the `2^20 - 26` squeeze-success ceiling, complete completion-schema preflight, exact length, state advance, acceptance/decode, retry bound, typed exhaustion, retained evaluator identity, and deterministic per-call work controls are closed |
| 7 | passed | Fresh and FS Schnorr execute over one literal Core with identity occurrence maps |
| 8 | passed at bounded finite-Oracle scope | native publication/query/answer is typed and replayable, and exact vectors form both present and absent answer bodies; the fixture runtime does not execute sparse absence or verifier-only Oracle visibility, while polynomial/oracle commitment and BCS correctness remain separate |
| 9 | passed | guard, schedule, role, failure, composition, extension, identity, admission, rejected-rival, and reopening effects are explicit |
| 10 | passed | the bounded gate, durable routing, manifest/link checks, final independent frozen follow-up, exactness-audit disposition, and repository non-regression commands are recorded below |

K2 is therefore narrowly reclosed at its bounded scope. This does not freeze
the integrated semantic kernel: K3 must test the read interfaces against Relations,
Analysis, and the minimum OIR projection-obligation view, and may reopen a K2
choice only with a concrete contradiction.

## 6. Final verification record

| Gate | Final result |
|---|---|
| K2 strict semantic instrument | 57/57 passing |
| K1 strict foundation instrument | 116/116 passing: 90 reference checks and 26 independent-oracle checks |
| R2 Protocol-model non-regression | 39/39 tests passing; canonical report identities and classifications reproduced |
| P01 Schnorr/Sigma non-regression | 69/69 tests passing; public report rebuilt, verified, and matched to the frozen projection |
| current compiler/lit suite | 171/171 lit tests and 50/50 C++ unit cases passing |
| Python lint for the K2 instrument | `ruff` passing |
| public-tree guard | passing; no development-repository paths tracked |
| durable manifest | 40/40 exact rows including the exceptional `notes/README.md` boundary |
| local Markdown targets | 1,390/1,390 parsed local file targets resolve |
| whitespace and patch integrity | `git diff --check` passing |

No generated fixture or accepted vector was rewritten by these commands.

This narrow reclosure changes the exact guard and Oracle-answer `FrameBody`
octets and tightens the transcript byte ceiling. It therefore supersedes the
earlier unshipped K2 draft law; no supported or deployed target byte stream is
being reinterpreted. Had the earlier frame law been frozen in a supported
semantic module or regime, that module or regime and every dependent ordinary
identity would have to rotate. The K5 freeze audit must treat this record as the
latest K2 frame-law movement, not assume identity continuity across the draft
change.

## 7. Explicit nonclaims and K3 handoff

K2 does not establish soundness, knowledge soundness, completeness, zero
knowledge, extraction, state-restoration or RBR soundness, ROM/QROM theorem
applicability, concrete security loss, hash/sponge security, challenge
distribution truth, oracle/commitment binding, BCS correctness, relation
satisfaction, compiler legality, OIR projection correctness, endpoint validity,
implementation conformance, or protocol-family completeness.

K3 receives only these PIR-owned read surfaces: exact bindings/scopes, strategy
decision coordinates and public histories, `PublicCoinView`, Oracle lifecycle,
claim/reduction structure, transcript declaration, required influence,
challenge transition, and checked Fresh/FS construction. K3 may define
Relations correspondence, adversary and theorem applicability, property
transport/loss, and minimum OIR obligations. It may not silently replace Core
or transcript meaning.
