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

A single narrow cold follow-up then rechecked only those seven original
blockers and four clarifications against the repaired owners and instrument.
It classified all seven as resolved and all four clarifications as satisfied,
and independently reran the 48-test K2 gate. This was a defect-disposition
check, not a new broad architecture or cryptographic-security audit.

## 4. Executable falsifier matrix

The strict runner executes 48 tests. The table records only what those finite
tests observe.

| Obligation | Positive control | Falsifier or contrast | State |
|---|---|---|---|
| same-Core Fresh/FS | Schnorr accepts under both interpretations with equal `CoreId` | construction identity changes with Core; Fresh carries no FS state | passed |
| causal strategy | honest prefix-only strategy completes and replays | future read and strategy stop are noncompletion; replay alone gains no causal provenance | passed |
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
| 4 | passed | full prefix equality and ordered required-influence inclusion cover message, Oracle, condition, guard, draw, reduction, and supported-module atoms |
| 5 | passed | occurrence/draw namespaces are derived; the finite dependency graph rejects verifier-private paths to FS-relevant sinks |
| 6 | passed | four one-result algorithms, exact length, state advance, acceptance/decode, retry bound, typed exhaustion, and deterministic work bounds are closed |
| 7 | passed | Fresh and FS Schnorr execute over one literal Core with identity occurrence maps |
| 8 | passed at bounded finite-Oracle scope | native publication/query/answer is typed and replayable; polynomial/oracle commitment and BCS correctness remain separate |
| 9 | passed | guard, schedule, role, failure, composition, extension, identity, admission, rejected-rival, and reopening effects are explicit |
| 10 | passed | the bounded gate, durable routing, manifest/link checks, final cold-audit disposition, and repository non-regression commands are recorded below |

K2 is therefore complete at its frozen bounded scope. This does not freeze the
integrated semantic kernel: K3 must test the read interfaces against Relations,
Analysis, and the minimum OIR projection-obligation view, and may reopen a K2
choice only with a concrete contradiction.

## 6. Final verification record

| Gate | Final result |
|---|---|
| K2 strict semantic instrument | 48/48 passing |
| K1 strict foundation instrument | 116/116 passing: 90 reference checks and 26 independent-oracle checks |
| R2 Protocol-model non-regression | 39/39 tests passing; canonical report identities and classifications reproduced |
| P01 Schnorr/Sigma non-regression | 69/69 tests passing; public report rebuilt, verified, and matched to the frozen projection |
| current compiler/lit suite | 171/171 lit tests and 50/50 C++ unit cases passing |
| Python lint for the K2 instrument | `ruff` passing |
| public-tree guard | passing; no development-repository paths tracked |
| durable manifest | 40/40 exact rows including the exceptional `notes/README.md` boundary |
| local Markdown targets | 1,335/1,335 local file targets resolve |
| whitespace and patch integrity | `git diff --check` passing |

No generated fixture or accepted vector was rewritten by these commands.

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
