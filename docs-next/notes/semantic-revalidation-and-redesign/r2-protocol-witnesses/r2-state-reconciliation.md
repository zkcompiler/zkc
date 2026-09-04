# R2 Phase A State Reconciliation

> **Kind:** Temporary R2 status and evidence reconciliation
> **State:** Phase A complete at the inspected working-tree snapshot; semantic
> repair is intentionally deferred to Phase B
> **Authority:** None. This page selects no Protocol, Relations, Analysis, or
> Compiler semantics and closes no protocol case.
> **Input baseline:** Git commit `5cdfe62` on `docs/semantic-redesign`, inspected
> 2026-08-24 before Phase A edits.
> **Scope:** Phase A snapshot status, protocol/probe naming, evidence strength,
> P01 closure blockers, and documentation routing.
> **Disposition:** Absorb stable status and evidence vocabulary into their
> durable owners after R2; delete this page with the temporary workspace.

## 1. Reconciled Phase A state

At the inspected Phase A snapshot, the reconciled status was:

> R1 is complete. R2 is active. The repaired `FRI-Grind-1` witness is closed
> only at its finite source-residual scope. The expressibility portfolio is
> selected. `P01` Schnorr/Sigma is active: source reconstruction, a provisional
> finite implementation, 40 passing unit tests, and a passing 16-case narrow
> oracle exist, but P01 has not closed T3. Portfolio cases `P02`--`P10`, recent
> variants `V01`--`V05`, and holdouts `H01`--`H05` have not begun. R3, R4, and
> Stage 4B remain inactive.

The R2 README owns the live program status. The portfolio owns case selection
and order. The Phase B decision now owns P01's current gate table; Section 4 of
this page preserves only the Phase A blocker summary. Historical baseline,
validation, and FRI cold-review records remain frozen descriptions of their own
checkpoints rather than being rewritten to match today.

## 2. Protocol cases and cross-cutting probes

`Pnn`, `Vnn`, and `Hnn` identify protocol cases, recent variants, and holdouts.
They are not generic experiment ordinals. Four packages that had been named as
if they were `P02`--`P05` are cross-cutting invariant probes and have been
reclassified without claiming portfolio progress:

| Former package | Phase A package | Code and semantic-ID namespace |
|---|---|---|
| `r2-p02-commitment` | `r2-probe-commitment` | `R2-CMT-*`, `r2.probe.commitment.*` |
| `r2-p03-logup` | `r2-probe-logup` | `R2-LOGUP-*`, `r2.probe.logup.*` |
| `r2-p04-bridges` | `r2-probe-value-bridges` | `R2-VBR-*`, `r2.probe.value-bridge.*` |
| `r2-p05-guards` | `r2-probe-guard-cost` | `R2-GUARD-*`, `r2.probe.guard.*` |

These probes may inform several cases and ledger invariants. None is a T1, T2,
or T3 protocol result. Their identity changes are intentional: no frozen report
or external replay contract used the former probe identities, and preserving a
false protocol classification would create continuing status ambiguity.

## 3. Evidence classes and Phase A measurements

The following classes are deliberately non-interchangeable:

1. **Frozen replay-verified corpus:** published cases reproduced under that
   witness's explicit frozen-input and replay contract.
2. **Published narrow case oracle:** published cases rebuilt by the same
   implementation and compared with stored expectations; coverage ends at the
   emitted case set.
3. **Unit-asserted behavior:** behavior a local suite reaches and asserts, with
   no implication that it is published or independently replayed.
4. **Live diagnostic snapshot:** measurements of the current checkout used to
   find gaps; not a durable result or closure decision.
5. **Declared but unreached surface:** result codes found in source but not
   fired by the instrumented current suite/report run; neither automatically a
   defect nor evidence that the path is impossible.

| Instrument | Phase A snapshot evidence | Exact non-claim |
|---|---|---|
| `FRI-Grind-1` | 41-case frozen replay-verified corpus; 39 passing tests | Stops at the named source residual; no authenticated FRI opening or terminal acceptance. |
| P01 | 16-case published narrow oracle; 40 passing tests | Does not publish execution, proof interface, qualification, exhaustive Analysis, or independent replay. |
| Commitment probe | 33 passing unit tests | Not `P02`; no frozen report. |
| LogUp probe | 29 passing unit tests | Not `P03`; no frozen report. |
| Value-bridge probe | 18 passing unit tests | Not `P04`; no frozen report. |
| Guard-cost probe | 22 passing unit tests | Not `P05`; no frozen report. |

At this snapshot, `evaluation/coverage.py` reports 3
`boundary-covered`, 15 `boundary-partial`, and 3 `boundary-uncovered` rows out
of 21 authored mappings. Those labels report observation of manually mapped
boundaries only. They do not say that an invariant is closed. The mapping pools
boundaries across witnesses, stored oracles, and live probes; positive support,
negative well-formedness, and semantic adequacy still require owner review.

The reachability diagnostic reports 566 declared result codes, 202 fired, and
364 unreached across the R2 instruments. P01 contributes 270 declared, 77
fired, and 193 unreached; its unreached codes cluster in `execution.py` (90),
`interface.py` (35), `relations.py` (34), `semantic.py` (33), and `report.py`
(1). This is consistent with the suite importing semantic, Relations, and
finite-Analysis surfaces but not exercising execution or the proof interface.
Reachability is a review queue, not a denominator for semantic completeness.

## 4. P01 closure finding

At the Phase A snapshot, no one of the ten then-proposed gates was fully
discharged by the 16-case oracle. The list below is the retained blocker
summary, not a current gate matrix. The
[Phase B decision](p01-phase-b-repair-and-refreeze.md#8-gate-decision) owns the
current gate states. The Phase A blockers were:

- **construction drift:** the document freezes a v1 transcript yielding
  `c=4,z=10`; the live code and fixture use a v2 runtime-context transcript
  yielding `c=0,z=4`;
- **private-evidence identity:** a public content digest directly commits to
  the toy witness and nonce, conflating an owner-local replay handle with a
  portable public identifier;
- **publication/source binding:** report sources are path strings rather than
  content digests, relevant sources are omitted, and the report root covers
  only the 16 emitted cases;
- **unintegrated surfaces:** execution, proof interface, qualification, and
  complete finite analyses exist in source but are not retained by the suite
  and report as required by T3;
- **incomplete negative pressure:** several named first boundaries lack a
  driver, one documented code did not exist, and some declared paths are
  structurally unreachable;
- **Relations grounding:** published cases stop at synthetic operands rather
  than grounding the separated judgments in an actual execution export; and
- **replay and review:** the runner rebuilds with the already-loaded
  implementation, `--repo-root` does not isolate source/fixture resolution,
  and no P01 cold-review packet exists.

Direct exploratory construction of Fresh/FS acceptance or a refusal is useful
for showing that modules are callable, but it does not close these retained-
evidence obligations.

## 5. Open obligations and routing

R1's [Review Adjudication](../review-adjudication.md) retains review findings;
the [Invariant Ledger](../invariant-ledger.md) owns solution-independent
requirements and falsifiers. The P01 page owns case-local design and closure.
The [Evaluation index](../../../../evaluation/README.md) owns executable-package
classification and diagnostic interpretation. This page owns only the Phase A
snapshot and must not become a competing semantic or issue ledger.

Phase B should begin from the blockers rather than from the present code shape:

1. compare the v1 and v2 FS constructions against primary sources and the
   cross-family requirements, then select one coherent finite construction;
2. redesign private owner-local authority, portable evidence identity, and
   evaluator/report source binding together;
3. integrate Fresh/FS execution, proof-interface verification, qualification,
   separated Relations judgments, exhaustive finite Analysis, and the complete
   negative matrix into one report design;
4. freeze a new evidence artifact only after all report inputs and identities
   are explicit;
5. perform context-isolated replay from copied public inputs; and
6. request a cold adversarial review of the resulting packet.

## 6. Review readiness and non-claims

P01 is not ready for a final validation request. A focused reviewer can already
challenge the construction choice, identity lanes, report closure, and matrix,
but a pass/fail cold gate should wait until gates 1--9 describe one candidate
rather than the current v1/v2 split.

Phase A does not repair strong Fiat--Shamir semantics, select an adversary
model, establish a cryptographic theorem, validate native FRI/IOR, close a
Relations correspondence, activate later stages, or claim implementation
support. It makes the state and the work queue honest enough for those later
decisions.

Phase A consistency checks passed for the P01 oracle, repaired FRI replay, all
five affected unit suites, coverage and reachability diagnostics, obsolete
probe-name absence, whitespace integrity, all 124 Markdown paths and directory
READMEs, the 37-entry durable manifest, all 11 temporary package indexes, and
the full `check-zkc` target (171 lit tests plus 50 C++ unit cases). These checks
validate the reconciliation mechanics, not the open semantic gates.

## 7. Deletion trigger

Delete this snapshot after its status vocabulary, namespace rules, P01 result,
and surviving work have been absorbed into durable owners and the R2 package no
longer needs a separate reconciliation checkpoint. Historical detail that is
not needed by a durable reader remains available in Git history.
