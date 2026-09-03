# Finite canonical-framed Fiat--Shamir runtime

> **State:** `CannotAnswer/F0V3C-C-FS-RUNTIME`; the complete finite candidate
> executes and replays, but one owner declaration body is absent.
> **Authority:** None. This research package edits no owner page, profile
> manifest, publication table, or normative identity registry.
> **Executable evidence:**
> [`evaluation/formal-source-fs-runtime-f0v3c`](../../../../evaluation/formal-source-fs-runtime-f0v3c/README.md)

## 1. Exact question and answer

Can the current canonical-framed owner text determine, admit, execute, and
independently replay one same-Core Fiat--Shamir construction over the admitted
finite Schnorr subject without an executor-local semantic choice?

Execution, replay, view reproduction, the six-lane partition, and the finite
derivation function are affirmative under one explicit candidate body. The
overall answer is nevertheless `CannotAnswer`: the owner text requires an
exact nominal application-domain body that its cited companion page does not
define. The package records the candidate choice visibly and refuses to treat
its dependent identities as owner-admitted.

## 2. Subject and admission boundary

The subject reuses the current target package's admitted additive `Z/3Z`
Schnorr Core and Fresh Protocol:

```text
Core:  zkcidv0:pir.interactive-core:dcb652fdca792d8664c51f2b98dca17d530607ff994c1eab15a59ed5c61cf2b8
Fresh: zkcidv0:pir.protocol:cc2fee36c903072621553a98fdb0d7bf3b84d13a18b0a51b04b7235367b7324f
```

The construction keeps that Core, uses one challenge rule with eight-byte
draws and a maximum of two draws, and forms the checked occurrence, value, and
challenge maps with sizes six, five, and one. Under the explicit proposed
application-domain body, the candidate identities are:

```text
TranscriptConstruction: zkcidv0:pir.transcript-construction:84873ab6046a1ec005fed9b90cdabb9b6532ffbba890b00dadad53558b94f4ee
FS Protocol:            zkcidv0:pir.protocol:83554765ae235514d1e77a72ca179315020c7d9efc320276a019ec6ce5827ae9
```

The same-Core checker reports `StructurallyConstructed`. That report means the
candidate maps and shared Core close under the checked construction rules. It
does not override the missing nominal declaration body or turn the candidate
identities into owner-issued identities.

## 3. Portable transition suite

The transcript state is `Bytes32`, transcript bytes are bounded to 4,096
octets, the natural count is the unsigned 64-bit carrier, and the initial state
is 32 zero octets. The suite consists of five canonical terms:

| Algorithm | Term meaning |
|---|---|
| `CanonicalFramedAbsorb` | SHA-256 of state concatenated with frame |
| `CanonicalFramedSqueezeBytes` | SHA-256-derived quartile selection among four exact eight-byte constants |
| `CanonicalFramedAdvanceState` | SHA-256 of state, namespace, count, and draw output concatenated in that order |
| `CanonicalFramedAccept` | first unsigned 64 bits of SHA-256(output) are below `3 * 2^62` |
| `CanonicalFramedDecode` | accepted quartiles map to `0`, `1`, and `2` in `Z/3Z` |

The package freezes each algorithm identity and `algorithm_preimage` digest.
Each body is type-checked, has an empty failure row and the exact executable-
foundations evaluation contract, and resolves only admitted primitive
references. Every evaluation authenticates that contract and the algorithm's
module dependency closure. Thus the candidate meaning is fixed by canonical
terms plus admitted primitive denotations; the executor supplies no separate
transition callback. The use of SHA-256 supplies deterministic finite behavior
only and carries no distribution, random-oracle, or security assertion.

## 4. Executor and independent replay

The generator initializes the transcript with `CoreHeader`,
`ConstructionHeader`, `ApplicationDomainHeader`, root `ScopeOpened`, and the
public statement binding. It then absorbs the first prover message, derives the
challenge namespace from construction, Core, scope path, challenge reference,
domain, value type, relationship, and draw ordinal, and runs the exact bounded
draw loop. Every draw records requested length, namespace, pre-state,
post-state, output, and acceptance.

An accepted draw produces the challenge receipt and resumes the Core engine.
Two rejected draws produce the typed sampling-exhausted payload and
`FSSamplingFailureReceipt` inside the `InterpretationFailure` completed-record
variant. Successful interpretation absorbs the response and terminal guard,
evaluates the admitted Schnorr check, and closes either the accepting or
rejecting terminal record.

The replay module does not import the executor. It separately implements frame
construction, namespaces, draw progression, occurrence execution, terminal
selection, and both completed-record variants. It compares the complete record
as an exact field set and also compares every transition receipt. All 54 runs
match. Surplus top-level data, a missing required record field, and a wrong
variant tag are each rejected.

## 5. Exhaustive finite result

The corpus contains all 27 private strategy triples `(statement, witness,
nonce)` and all 27 public verifier triples `(statement, commitment, response)`
over `Z/3Z`. The lane partition is total and exclusive:

| Lane | Count |
|---|---:|
| `Accepted` | 24 |
| `Rejected` | 24 |
| `Aborted` | 0 |
| `InterpretationFailed` | 6 |
| `StrategyStopped` | 0 |
| `OperationalNoncompletion` | 0 |

Six cases exhaust exactly two draws. They remain interpretation failures with
their full receipts; no transition parameter was retuned to erase that lane.
Among successful derivations, 18 produce value 0 in one draw, 18 produce value
2 in one draw, six produce value 1 in one draw, and six produce value 0 in two
draws.

`expected-runs.json` freezes every case, lane, completed-record digest,
transcript-prefix digest, and derivation result. `derivation-vectors.json`
factors the exact fixed, statement, and commitment frames and enumerates all
nine distinct `(challenge, statement, transcript prefix)` inputs. Each maps to
one decoded value or exact exhaustion. Its digest is
`7de05a0abcd11be065ad80fa1fd761850778a6ce9a6698b234583e2c00729575`.

## 6. View reproduction

The candidate derives `CanonicalTranscriptDeclarationView`,
`CanonicalRequiredInfluenceView`, `CanonicalChallengeTransitionView`, and
`CanonicalFSConstructionView`. Both current schema compilers from the
predecessor family-view package accept each value and agree on all four schema
digests. The package also derives the execution view with its exact protocol,
Core, construction, resolver-coordinate, run-record, interpretation-failure,
outcome-partition, replay, and relation-run issuance fields.

This checks schema conformance and deterministic derivation from the candidate.
It does not establish that the unresolved candidate declaration body has been
selected or published by an owner.

## 7. Findings

| Contract clause | Frozen result |
|---|---|
| admission | `CannotAnswer/F0V3C-C-APPLICATION-DOMAIN-BODY` |
| execution | `Affirmative/F0V3C-A-FINITE-EXECUTION` |
| replay | `Affirmative/F0V3C-A-INDEPENDENT-REPLAY` |
| views | `Affirmative/F0V3C-A-VIEW-REPRODUCTION` |
| outcome partition | `Affirmative/F0V3C-A-SIX-LANE-PARTITION` |
| derivation function | `Affirmative/F0V3C-A-DERIVATION-VECTORS` |
| aggregate | `CannotAnswer/F0V3C-C-FS-RUNTIME` |

The affirmative clause findings are bounded facts about the explicit candidate
and complete finite corpus. The entry contract permits an affirmative aggregate
only if no underdetermination remains, so the admission finding controls the
aggregate.

## 8. Proposed delta

**Owner page and section:** `docs-next/pir/interactive-core.md`, Section 2
owner profile and module declarations, with the recognized reference-kind list
at lines 2256--2259 remaining its downstream use; the requirement is cited by
`docs-next/pir/fiat-shamir.md` lines 68--71.

**Exact change:** Define the nominal declaration body for every local catalog
entry of kind `pir.fs-application-domain` to be exactly
`R { 0: Q(application_domain_symbol) }`, where
`application_domain_symbol` is a nonempty ASCII `MetaSymbol`; forbid surplus
fields. State that `ProtocolDeclarationRef<"pir.fs-application-domain">`
continues to use the existing exact module-declaration reference body. The
finite candidate instantiates the symbol as `finite-schnorr-runtime`.

**Identity effect:** This selects the bytes currently supplied only by the
candidate. Adoption would determine the application module identity,
transcript-construction identity, Fiat--Shamir Protocol identity, and every
view or downstream artifact that closes over them. The reused Core and Fresh
Protocol identities do not change under this separate exact-used module. A
different body or ownership placement requires regenerating the full dependent
identity cone.

**Evidence with gate ids:**
`CannotAnswer/F0V3C-C-APPLICATION-DOMAIN-BODY` isolates the missing body;
`Affirmative/F0V3C-A-FINITE-EXECUTION`,
`Affirmative/F0V3C-A-INDEPENDENT-REPLAY`,
`Affirmative/F0V3C-A-VIEW-REPRODUCTION`,
`Affirmative/F0V3C-A-SIX-LANE-PARTITION`, and
`Affirmative/F0V3C-A-DERIVATION-VECTORS` show that this exact candidate body
composes with all remaining bounded obligations.

**Reversal condition:** Withdraw or revise this delta if the owner selects a
different exact nominal body, allows a different symbol carrier or field set,
or assigns the declaration to a different authenticated module closure. Then
regenerate the module, construction, Protocol, views, run digests, and
derivation vectors and rerun both execution paths.

**Non-claims:** The proposed grammar is not adopted semantics, publication, a
uniqueness proof, or evidence that this application symbol is appropriate for
another protocol. The finite runtime evidence does not authorize the delta.

## 9. Result boundary

This package establishes candidate construction, exhaustive finite execution,
independent exact-record replay, view-schema conformance, measured outcome
counts, and a machine-readable derivation function. It does not establish
owner admission or publication, arbitrary-Core behavior, general evaluator
correctness, compiler/backend/runtime correspondence, provider
correspondence, relation truth, theorem applicability, protocol soundness,
zero knowledge, Fiat--Shamir security, random-oracle or quantum-random-oracle
security, concrete-hash suitability, duplex-sponge behavior, or production
readiness.

## Handoff

Main should commit the complete working tree with subject
`test: execute the migrated canonical-framed construction on the finite schnorr core`.

Files changed:

- `evaluation/formal-source-fs-runtime-f0v3c/README.md`
- `evaluation/formal-source-fs-runtime-f0v3c/model.py`
- `evaluation/formal-source-fs-runtime-f0v3c/executor.py`
- `evaluation/formal-source-fs-runtime-f0v3c/replay.py`
- `evaluation/formal-source-fs-runtime-f0v3c/views.py`
- `evaluation/formal-source-fs-runtime-f0v3c/run.py`
- `evaluation/formal-source-fs-runtime-f0v3c/expected-findings.json`
- `evaluation/formal-source-fs-runtime-f0v3c/expected-runs.json`
- `evaluation/formal-source-fs-runtime-f0v3c/derivation-vectors.json`
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v3c-fs-runtime.md`
- `checks/manifest.json`
- `evaluation/lifecycle.json`
- `evaluation/README.md`
- `checks/tests/test_evaluation_lifecycle.py`

The lifecycle-sensitive commands used a clone-local alternate index, a
clone-local writable object directory with the checkout objects as read-only
alternates, and an offline dependency cache under ignored `target/`. The real
Git index was never modified.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| Initial `python3 -B checks/run.py validate` | 2 | 0.2 s | The manifest correctly refused the unsupported method label `replay`; the entry was changed to the supported differential and bounded-exhaustive method vocabulary without changing the experiment. |
| Final `python3 -B checks/run.py validate` under the alternate index | 0 | 0.2 s | The 77-check, six-tier manifest is valid. |
| `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B checks/run.py run --tier developer` under the alternate index | 0 | 2.94 s | Nine of nine checks passed; lifecycle inventory reports 60 research checks, 62 packages, and 34 active-sequence dispositions. |
| `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B checks/run.py run --check research.fs-runtime` under the alternate index | 0 | 193.33 s | One of one check passed; the inner package check took 193.262 s and reproduced all frozen outputs. |
| Python source/JSON parse and `git diff --check` | 0 | 0.3 s | All new sources parse, all JSON files decode, and no whitespace error is present. |

Aggregate outcome: `CannotAnswer/F0V3C-C-FS-RUNTIME`. Six clauses have the
bounded outcomes listed above, and the missing application-domain declaration
body prevents owner admission and the affirmative aggregate.

Non-claims: no owner-page adoption, profile or identity publication,
arbitrary-subject runtime result, implementation or provider correspondence,
theorem, protocol or cryptographic security, or production-readiness result.

Surprises and corrections to the brief: the entry contract abbreviates the
Core with a stale `0e767c0c...` digest, while the live target package admits the
`dcb652fd...` Core used here; the requested separate
`evaluation/formal-source-owner-view-fs-family-bodies` directory does not
exist, because those family-view bodies are integrated into
`evaluation/formal-source-fs-view-determinacy-f0v3`; and this clone omits
`AGENTS.md` and `.claude/CLAUDE.md`, so their read-only primary-checkout copies
supplied the required instructions. The workflow's private ledger append is
also superseded by the explicit prohibition on writes outside this clone. The
manifest method vocabulary has no separate `replay` label; replay remains the
experiment's independently implemented differential method and the manifest
uses supported method names.

The real Git index remains untouched. No commit, push, pull request, owner-page
edit, profile-manifest edit, directory-README edit, publication, or private-
ledger write was attempted.
