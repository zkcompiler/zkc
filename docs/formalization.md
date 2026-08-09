# Formalization Evidence

zkc records attributed formalization evidence beside Soundness Kernel rules.
The current mechanism checks receipts and source drift. It does not yet connect
a concrete PIR subject to a theorem-prover statement.

## Current model

Every rule in the soundness signature records one of two states:

- a **formalization receipt** naming an external repository, revision,
  declaration, printed statement when available, axiom profile, and covered
  obligation slots; or
- a **surveyed absence** naming the statement sought and the exact demand that
  remains unmet.

The signature loader validates these annotations and requires every rule to
record one of the two states. Annotations are deliberately outside the
executable rule catalog and its content identity. They cannot discharge a
premise, change a bound, or alter a derivation result.

## Mechanization demand

A theorem-backed end-to-end judgment needs the following chain. The labels in
the right column report the reading at the ArkLib revision in
[`arklib-pin.txt`](../arklib-pin.txt).

| Link | Required statement | Current reading |
|---|---|---|
| Entry | Sumcheck round-by-round soundness | subject incomplete |
| Entry | Random-query round-by-round soundness | proof incomplete |
| Entry | Sigma special soundness | absent |
| Entry | Per-round FRI soundness | absent |
| Entry | GKR-layer round-by-round soundness | absent |
| Entry | KZG computational special soundness | absent |
| Hop | Special soundness to round-by-round soundness | absent |
| Hop | Round-by-round to state restoration | proof incomplete |
| Hop | State restoration to duplex Fiat-Shamir | absent |

A missing link prevents composing the receipts into a theorem-backed
end-to-end result. It does not invalidate the available component statements
or prevent a separately reviewed conditional analysis.

### Fiat-Shamir

Rules `zkc.fs.duplex` and `zkc.fs.duplex_knowledge` require a duplex
Fiat-Shamir theorem of the form

```text
eps_fs(t) <= eps_sr(t) + 25 t^2 / |Sigma|^c
             + t * max_i eps_cdc_i + sum_i eps_cdc_i
```

Here `Sigma` is the sponge alphabet, `c` is the capacity, and `eps_cdc_i` is
the squeeze bias at challenge event `i`. zkc obtains those quantities from the
sealed artifact. ArkLib contains supporting duplex-sponge machinery, but no
closing state-restoration-to-Fiat-Shamir theorem at the current pin.

### State restoration

Rules `zkc.sr.from_rbr` and `zkc.sr.from_rbr_knowledge` require the
move-budget implication `eps_sr(t) <= t * eps_rbr`. ArkLib contains the
relevant definitions and implication statements, but their proofs remain
incomplete at the current pin. The zkc rules also require the bound to be
uniform over the admitted salt treatment.

### Special soundness to round-by-round

Rule `zkc.rbr.from_ss` requires the per-round implication
`eps_i = (k_i - 1) / |C_i|`. ArkLib has useful special-soundness and
coordinate-wise composition results; the implication into the required
round-by-round judgment is not present at the current pin.

### Entry theorems

| zkc rule family | Required statement | Current reading |
|---|---|---|
| `zkc.ss.sigma` | special soundness for the admitted Sigma shapes | absent |
| `zkc.rbr.fri.*` | per-fold and per-query round-by-round FRI soundness | absent |
| `zkc.rbr.gkr-width2-layer` | round-by-round soundness for one admitted GKR layer | absent |
| `zkc.rbr.ordered_rlc` | ordered random-linear-combination bound | absent |
| `zkc.rbr.grinding` | selected-round proof-of-work scaling | absent |
| `zkc.pcs.kzg_css` | KZG computational special soundness under ARSDH | absent |
| `zkc.pcs.kzg_batch*.v*` | same-point batching preservation | absent |
| `zkc.rbr.r1cs_batch` | admitted R1CS batching-round bound | absent |

The chain rules `zkc.rbr.gkr-width2-chain` and
`zkc.rbr.r1cs_sumcheck-chain` do have receipts for ArkLib sequential
composition declarations. Their recorded state is `subject_incomplete`
because the cited oracle-verifier subject depends on an admitted definition.

### FRI

ArkLib contains monolithic batched-FRI soundness statements. zkc's current
rule chain instead needs a per-round error family that can compose with later
round-by-round and Fiat-Shamir hops. That statement is not available at the
pin. The constants used by the current zkc rules and ArkLib's aggregate FRI
statement refer to different aggregation levels and are not treated as a
discrepancy.

### KZG

ArkLib defines ARSDH and tSDH assumptions and contains mechanized KZG binding
results. The current zkc demand is narrower and stronger in a different
direction: computational special soundness or straight-line extraction,
same-point batching preservation, and the required assumption correspondence.
Those statements are not available at the pin.

## ArkLib receipts

For receipts that point to ArkLib, the reading procedure asks Lean for the
declaration's printed type and axiom dependency set and compares the normalized
result with the recorded annotation.

| Receipt state | Meaning |
|---|---|
| `mechanized` | The declaration reproduced without a `sorryAx` dependency. |
| `proof_incomplete` | The declaration reproduced with a proof hole while its subject was available. |
| `subject_incomplete` | The declaration reproduced, but its formal subject depended on an incomplete definition. |

At the current pin, six ArkLib receipts are checkable by the driver:

| State | Declarations |
|---|---|
| `mechanized` | `RandomQuery.oracleReduction_completeness` |
| `proof_incomplete` | `RandomQuery.oracleVerifier_rbrKnowledgeSoundness`; `Sumcheck.Spec.reduction_perfectCompleteness` |
| `subject_incomplete` | `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness`; `OracleVerifier.seqCompose_rbrSoundness`; `OracleVerifier.seqCompose_rbrKnowledgeSoundness` |

Four additional receipts point outside the pinned ArkLib checkout and are
reported but not checked by this procedure. Sixteen rules carry surveyed
absence records instead. These counts describe the current signature, not
ArkLib as a whole.

## Reproduce the reading

The ordinary test suite validates receipt shape, pins, coverage fields, and
state/axiom consistency without fetching Lean or ArkLib:

```sh
python3 test/Soundness/Inputs/formalization_receipts.py \
  registry/soundness-signature.json
```

For the external reading, build an ArkLib checkout at the exact
`arklib-pin.txt` revision and run:

```sh
python3 test/Soundness/Inputs/formalization_receipts.py \
  registry/soundness-signature.json --checkout /path/to/ArkLib
```

The driver refuses a checkout at another revision, builds the modules needed
by the receipts, runs `#check` and `#print axioms`, and refuses changed
statements or axiom profiles. The separate `Lean reading` workflow automates
the same pinned operation.

When the pin moves, a removed declaration, changed type, or changed axiom
profile requires a new correspondence review. A pin update with no observed
statement or axiom-profile change is not itself a formalization advance.

## What remains for a formal bridge

A theorem-backed compiler judgment requires:

1. a precise formal subject for the concrete PIR component or occurrence;
2. a checked correspondence between that subject and the zkc rule obligation;
3. an evidence envelope authenticating the theorem, environment, and scope;
4. an admission policy deciding which exact compiler claim may consume it;
   and
5. where required, correspondence from the compiled endpoint to the deployed
   implementation.

The [roadmap](roadmap.md#connect-formal-evidence) places this component-wise
bridge after the relevant semantic contracts stabilize. Receipt and absence
metadata remains useful provenance until then.

## Non-claims

A receipt or successful drift check does not prove that:

- the external declaration faithfully models a PIR component;
- the executable zkc rule faithfully implements that declaration;
- the theorem applies to a particular sealed artifact or endpoint;
- all composition, Fiat-Shamir, interleaving, or backend obligations close; or
- the whole protocol is sound, complete, zero knowledge, or implementation
  correct.

The signature annotations own the receipt contents, pin files own source
revisions, and the reading output records an observation of those pinned
sources. None of these surfaces alone is an admission result.
