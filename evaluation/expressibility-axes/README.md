# R-A structural expressibility axes

> **Check ID:** `research.expressibility-axes`
> **Lifecycle:** `retained-bounded-instruments`
> **Aggregate:** `Affirmative/RA-A-AXES-CLOSED-AND-DERIVED`

## Exact question

Does one closed structural-feature vocabulary, with every value routed to one
current constructor or profile, one listed Core reopening condition, or one
explicit boundary, deterministically classify every frozen case without using
protocol-family names as rules?

## Frozen inputs

[`axes.json`](axes.json) contains 20 closed axes and 125 closed values. Every
value has exactly one of 40 destinations: 23 current Core/profile constructors,
five listed reopening conditions, or 12 explicit boundaries. The destination
records name their owner page and section. The checker pins the four referenced
PIR pages and the post-freeze program README; this package does not edit or
supersede them.

The termination-axis meaning for canonical interpretation failure is corrected
to match the migrated owner contract: it is a separate completed failure
record and outcome lane, never a Core terminal. This wording-only correction
does not change any case vector, destination, derived verdict, or frozen
finding; the owner-page pins now name the migrated page bytes.

[`cases.json`](cases.json) is a 63-row matrix with exactly one cell for every
axis in every row. It covers all `P01`--`P10`, `V01`--`V05`, and `H01`--`H05`
portfolio identifiers, including separate rows where a portfolio cluster or
holdout adjudication contains materially different structural shapes. It also
freezes the 20-row peer-review pressure map as 22 rows after splitting shared
versus imported challenges and virtual distributed proving versus true
noncommunicating multiprover interaction.

The private peer-review note is not copied into this package. `cases.json`
records its path, SHA-256 digest, exact row coordinates, labels, structural
projections, and required destinations. The checker uses that frozen extract,
so it remains runnable in a public clone without pretending that the private
document is distributed authority.

The additional source-pressure rows are grounded in the following primary
sources:

- designated-verifier preprocessing: [QuickSilver](https://eprint.iacr.org/2021/076.pdf);
- delay proofs: [Wesolowski](https://eprint.iacr.org/2018/623.pdf) and
  [Pietrzak](https://eprint.iacr.org/2018/627.pdf);
- commit-and-prove: [LegoSNARK](https://eprint.iacr.org/2019/142);
- PCP-based arguments and proofs: [Kilian](https://doi.org/10.1145/129712.129782)
  and [Micali](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Proof%20Systems/Computationally_Sound_Proofs.pdf);
- verifiable computation over encrypted data:
  [Fiore--Gennaro--Pastro](https://eprint.iacr.org/2014/202.pdf);
- anonymous-credential lifecycle:
  [Camenisch--Lysyanskaya](https://www.iacr.org/archive/eurocrypt2001/20450093.pdf);
- dynamic interactive-machine termination pressure:
  [Goldwasser--Micali--Rackoff](https://doi.org/10.1145/22145.22178);
- private coins:
  [Goldwasser--Sipser](https://www.cs.toronto.edu/tss/files/papers/goldwasser-Sipser.pdf);
- noncommunicating multiprover interaction:
  [Ben-Or--Goldwasser--Kilian--Wigderson](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/GKBW88/GKBW88.pdf);
- distributed verifier knowledge:
  [distributed interactive proofs with shared and private randomness](https://arxiv.org/abs/2006.16191); and
- quantum interaction: [Watrous](https://arxiv.org/abs/cs/9901015).

The GMR row is expressly model-level pressure for a prover-chosen continuation
count. It does not attribute that feature to GMR's named zero-knowledge
protocol.

## Derivation

The runner does not store a family-to-verdict table. It repeatedly resolves
each selected feature value through `axes.json`, deduplicates the destinations,
and applies one precedence rule:

1. any `explicit_boundary` destination yields `breaks` and reports all selected
   boundary IDs;
2. otherwise, any `reopening_condition` destination yields `bends` and reports
   all selected reopening IDs; and
3. otherwise every value reaches a current constructor and the row `fits`.

`Undetermined` is not silently upgraded. A frozen `Undetermined` adjudication
agrees only when the feature vector reaches the exact source or cross-execution
boundary that prevented an answer. Missing source semantics therefore remain a
boundary-shaped `CannotAnswer`, not a negative protocol claim.

The runner validates duplicate-free strict JSON, closed schemas, total
destination routing, owner headings and source hashes, complete feature
vectors, canonical multivalue cells, portfolio/peer/unconsidered censuses,
primary-source coordinates, frozen predictions, and recorded-adjudication
projections. Six internal mutations must fail: an unknown destination, a short
vector, an unknown value, a noncanonical multivalue cell, a substituted
prediction, and a substituted recorded verdict.

## Run

From the repository root:

```sh
python3 -B evaluation/expressibility-axes/run.py --check
python3 -B checks/run.py run --check research.expressibility-axes
```

The first command compares the complete finding projection and canonical
finding digest with [`expected-findings.json`](expected-findings.json). A
prediction or recorded-verdict disagreement changes the aggregate to
`CannotAnswer/RA-C-RECORDED-VERDICT-DISAGREEMENT`; malformed or drifting input
fails closed before an aggregate is accepted.

## What a pass establishes

A pass establishes only that, for the pinned owner text and authored source
readings, the closed 20-axis matrix is total over all 63 frozen rows; every cell
resolves to exactly one named destination; the precedence rule reproduces all
frozen row predictions; and the eight holdout and 22 peer-review records have
no structural-verdict or obstruction disagreement.

## What a pass does not establish

A pass does not establish that the axes are universally complete, that a new
protocol was read correctly, that any family or implementation is supported,
that a profile or module is implemented, that an imported verifier is correct,
or that any relation, theorem, soundness, knowledge, zero-knowledge,
Fiat--Shamir, setup, composition, or deployment claim is true. The primary
citations support authored feature assignments only; they are not a
machine-checked source-correspondence result. `fits` means structural placement
in the current model, not cryptographic acceptance or product readiness.
