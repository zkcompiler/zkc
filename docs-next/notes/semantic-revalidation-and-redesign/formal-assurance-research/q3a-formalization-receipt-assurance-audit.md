# Q3-A formalization-receipt assurance audit

> **Kind:** Temporary formal-assurance research note
> **State:** Complete at bounded research resolution
> **Cutoff:** `faea36ef6da3f82e29ff5fddc6750a4824bfbc2a`
> **Authority:** None. No semantic owner, Analysis judgment, theorem status,
> target profile, implementation claim, or user gate changes here.

## Question and result

The audit asks whether the existing ArkLib `FormalizationReceipt` reading can
form an independently authenticated Q3 environment result for its six live
declarations. The executable package is
[`evaluation/formalization-receipt-assurance-q3a/`](../../../../evaluation/formalization-receipt-assurance-q3a/README.md).

The result is
`CannotAnswer/Q3A-C-OBSERVATION-NOT-AUTHENTICATED-RESULT`.
A clean exact-pin Lean run reproduced all six normalized statements and axiom
sets. The current mechanism nevertheless stops at a useful source-drift
observation: it does not emit a durable typed result that binds the complete
environment, checker mode, identity, outcome partition, and residual trust.

## Findings that affect later design

- The current reading is real evidence, not a citation-only bookmark. At the
  ArkLib pin, all six declarations resolve and agree with their receipts.
- `#print axioms` distinguishes a `sorryAx`-free closure from one containing a
  hole. It does not identify whether that hole is in the proof or in the
  theorem's subject. Both directions of
  `proof_incomplete`/`subject_incomplete` relabeling pass the driver.
- `covers` and `does_not_cover` are reviewed correspondence annotations. The
  driver checks only that `covers` is nonempty; it cannot derive either scope
  from the theorem statement.
- The ordinary no-checkout path validates shape, pin, and `sorryAx` polarity,
  but does not authenticate the recorded statement or complete axiom set.
- Four receipts outside ArkLib remain outside this reading procedure.
- A fresh workflow checkout supplies useful operational isolation, but the
  result does not bind clean-tree evidence, tree and dependency identities,
  imported modules, toolchain, checker source/mode, or a canonical result ID.
- The official workflow is active but had no public run records at the dated
  inspection. A separately reproduced local exact-pin run is frozen as a
  research observation, not promoted into a workflow result.

## Decision inputs, not a selected direction

The current drift-reader role can remain as-is if its claim is kept narrow. A
separate Q3 result becomes necessary only when Analysis or another consumer
needs an authenticated theorem-environment fact rather than provenance.

The smallest candidate result would bind the exact repository/revision/tree,
dependency lock and toolchain, modules, declaration, statement, axiom profile,
checker source and mode, and source identities, then preserve qualified
failure classes and produce a canonical result ID. Fresh kernel replay such as
`lean4checker --fresh`, and comparator or independent-checker validation, are
additional trust-policy choices rather than one mandatory design.

No environment mechanism can close the semantic edges by itself.
`proof_incomplete` versus `subject_incomplete` needs hole-provenance analysis;
coverage needs Q2 or Q5 correspondence; property use still needs separate Q4,
Q5, and Q6 judgments. The existing Q0--Q10 separation therefore survives the
audit unchanged.

## Frozen evidence

```sh
python3 -B evaluation/formalization-receipt-assurance-q3a/run.py --check
```

The branch-local result is 29 findings: nine affirmative, five refused, and
fifteen `CannotAnswer`. The direct registry/environment model and the
black-box production-driver mutation path share no receipt-validation code.
